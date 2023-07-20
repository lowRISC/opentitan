// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwm.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/dif/dif_base.h"

#include "pwm_regs.h"  // Generated.

static_assert(PWM_PARAM_N_OUTPUTS == 6,
              "Expected six PWM channels. May need to update `dif_pwm.h`.");
static_assert(PWM_CFG_DC_RESN_MASK == 0xf,
              "Expected duty cycle configuration register to be 4 bits.");

dif_result_t dif_pwm_configure(const dif_pwm_t *pwm, dif_pwm_config_t config) {
  if (pwm == NULL || config.clock_divisor > PWM_CFG_CLK_DIV_MASK ||
      config.beats_per_pulse_cycle < 2 ||
      config.beats_per_pulse_cycle > (1U << 16)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(pwm->base_addr, PWM_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // We do a read-modify-write to restore the enablement state of the phase
  // counter enablement bit, after temporarily disabling it to update the
  // other configuration register fields.
  uint32_t config_reg = mmio_region_read32(pwm->base_addr, PWM_CFG_REG_OFFSET);
  config_reg = bitfield_field32_write(config_reg, PWM_CFG_CLK_DIV_FIELD,
                                      config.clock_divisor);

  // Since `beats_per_pulse_cycle` = 2 ^ (`duty_cycle_resolution` + 1), we can
  // compute the duty cycle resolution by:
  //
  // `DC_RESN` = log2(`beats_per_pulse_cycle`) - 1
  //
  // To compute the log2, we can find the index of the most-significant 1-bit,
  // the lastly, subtract 1.
  uint32_t dc_resn_val = 30u - (uint32_t)bitfield_count_leading_zeroes32(
                                   config.beats_per_pulse_cycle);
  config_reg =
      bitfield_field32_write(config_reg, PWM_CFG_DC_RESN_FIELD, dc_resn_val);

  // Clear the phase counter enable bit before updating the register.
  mmio_region_write32(pwm->base_addr, PWM_CFG_REG_OFFSET, 0);
  mmio_region_write32(pwm->base_addr, PWM_CFG_REG_OFFSET, config_reg);

  return kDifOk;
}

dif_result_t dif_pwm_configure_channel(const dif_pwm_t *pwm,
                                       dif_pwm_channel_t channel,
                                       dif_pwm_channel_config_t config) {
  if (pwm == NULL || (config.polarity != kDifPwmPolarityActiveHigh &&
                      config.polarity != kDifPwmPolarityActiveLow)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(pwm->base_addr, PWM_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // Configure duty cycle register.

  // Get "beats_per_pulse_cycle" from the PWM config register.
  // There are 2 ^ (`duty_cycle_resolution` + 1) "beats" per "pulse cycle".
  uint8_t duty_cycle_resolution = (uint8_t)bitfield_field32_read(
      mmio_region_read32(pwm->base_addr, PWM_CFG_REG_OFFSET),
      PWM_CFG_DC_RESN_FIELD);
  uint32_t beats_per_pulse_cycle = 1U << (duty_cycle_resolution + 1);

  // Check duty cycle and phase delay configurations.
  if (config.duty_cycle_a >= beats_per_pulse_cycle ||
      config.duty_cycle_b >= beats_per_pulse_cycle ||
      config.phase_delay >= beats_per_pulse_cycle) {
    return kDifBadArg;
  }

  // There are 2 ^ 16 "phase counter ticks" in one "pulse cycle", and therefore
  // 2 ^ (16 - `duty_cycle_resolution` - 1) "phase counter ticks" in one "beat".
  uint16_t phase_cntr_ticks_per_beat =
      (uint16_t)(1 << (16 - duty_cycle_resolution - 1));
  uint32_t duty_cycle_reg =
      bitfield_field32_write(0, PWM_DUTY_CYCLE_0_A_0_FIELD,
                             phase_cntr_ticks_per_beat * config.duty_cycle_a);
  duty_cycle_reg =
      bitfield_field32_write(duty_cycle_reg, PWM_DUTY_CYCLE_0_B_0_FIELD,
                             phase_cntr_ticks_per_beat * config.duty_cycle_b);

  // Configure parameter register.
  uint32_t param_reg =
      bitfield_field32_write(0, PWM_PWM_PARAM_0_PHASE_DELAY_0_FIELD,
                             phase_cntr_ticks_per_beat * config.phase_delay);
  if (config.mode == kDifPwmModeHeartbeat) {
    param_reg =
        bitfield_bit32_write(param_reg, PWM_PWM_PARAM_0_HTBT_EN_0_BIT, true);
  } else if (config.mode == kDifPwmModeBlink) {
    param_reg =
        bitfield_bit32_write(param_reg, PWM_PWM_PARAM_0_BLINK_EN_0_BIT, true);
  }

  // Configure polarity register.
  uint32_t invert_reg =
      mmio_region_read32(pwm->base_addr, PWM_INVERT_REG_OFFSET);

  // Configure blink mode parameter register.
  uint32_t blink_param_reg = 0;
  if (config.mode == kDifPwmModeHeartbeat || config.mode == kDifPwmModeBlink) {
    blink_param_reg = bitfield_field32_write(
        blink_param_reg, PWM_BLINK_PARAM_0_X_0_FIELD, config.blink_parameter_x);
    if (config.mode == kDifPwmModeHeartbeat) {
      if (config.blink_parameter_y >= beats_per_pulse_cycle) {
        return kDifBadArg;
      }
      // Convert "beats" to "phase counter ticks", since this value is added to
      // the duty cycle (which hardware computes in "phase counter ticks").
      blink_param_reg = bitfield_field32_write(
          blink_param_reg, PWM_BLINK_PARAM_0_Y_0_FIELD,
          phase_cntr_ticks_per_beat * config.blink_parameter_y);
    } else if (config.mode == kDifPwmModeBlink) {
      blink_param_reg =
          bitfield_field32_write(blink_param_reg, PWM_BLINK_PARAM_0_Y_0_FIELD,
                                 config.blink_parameter_y);
    }
  } else if (config.mode != kDifPwmModeFirmware) {
    return kDifBadArg;
  }

#define DIF_PWM_CHANNEL_CONFIG_CASE_(channel_)                                 \
  case kDifPwmChannel##channel_:                                               \
    invert_reg = bitfield_bit32_write(                                         \
        invert_reg, PWM_INVERT_INVERT_##channel_##_BIT, config.polarity);      \
    mmio_region_write32(pwm->base_addr,                                        \
                        PWM_DUTY_CYCLE_##channel_##_REG_OFFSET,                \
                        duty_cycle_reg);                                       \
    mmio_region_write32(pwm->base_addr, PWM_PWM_PARAM_##channel_##_REG_OFFSET, \
                        param_reg);                                            \
    if (config.mode == kDifPwmModeHeartbeat ||                                 \
        config.mode == kDifPwmModeBlink) {                                     \
      mmio_region_write32(pwm->base_addr,                                      \
                          PWM_BLINK_PARAM_##channel_##_REG_OFFSET,             \
                          blink_param_reg);                                    \
    }                                                                          \
    break;

  switch (channel) {
    DIF_PWM_CHANNEL_LIST(DIF_PWM_CHANNEL_CONFIG_CASE_)
    default:
      return kDifBadArg;
  }
#undef DIF_PWM_CHANNEL_CONFIG_CASE_

  mmio_region_write32(pwm->base_addr, PWM_INVERT_REG_OFFSET, invert_reg);

  return kDifOk;
}

dif_result_t dif_pwm_phase_cntr_set_enabled(const dif_pwm_t *pwm,
                                            dif_toggle_t enabled) {
  if (pwm == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(pwm->base_addr, PWM_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  uint32_t config_reg = mmio_region_read32(pwm->base_addr, PWM_CFG_REG_OFFSET);
  config_reg = bitfield_bit32_write(config_reg, PWM_CFG_CNTR_EN_BIT,
                                    dif_toggle_to_bool(enabled));
  mmio_region_write32(pwm->base_addr, PWM_CFG_REG_OFFSET, config_reg);

  return kDifOk;
}

dif_result_t dif_pwm_phase_cntr_get_enabled(const dif_pwm_t *pwm,
                                            dif_toggle_t *is_enabled) {
  if (pwm == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t config_reg = mmio_region_read32(pwm->base_addr, PWM_CFG_REG_OFFSET);
  *is_enabled =
      dif_bool_to_toggle(bitfield_bit32_read(config_reg, PWM_CFG_CNTR_EN_BIT));

  return kDifOk;
}

dif_result_t dif_pwm_channel_set_enabled(const dif_pwm_t *pwm,
                                         uint32_t channels,
                                         dif_toggle_t enabled) {
  if (pwm == NULL || channels >= (1U << PWM_PARAM_N_OUTPUTS) ||
      !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(pwm->base_addr, PWM_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  uint32_t enable_reg =
      mmio_region_read32(pwm->base_addr, PWM_PWM_EN_REG_OFFSET);

  if (dif_toggle_to_bool(enabled)) {
    enable_reg |= channels;
  } else {
    enable_reg &= ~channels;
  }

  mmio_region_write32(pwm->base_addr, PWM_PWM_EN_REG_OFFSET, enable_reg);

  return kDifOk;
}

dif_result_t dif_pwm_channel_get_enabled(const dif_pwm_t *pwm,
                                         dif_pwm_channel_t channel,
                                         dif_toggle_t *is_enabled) {
  if (pwm == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t channel_bit = (uint32_t)bitfield_count_trailing_zeroes32(channel);

  if (channel_bit >= PWM_PARAM_N_OUTPUTS) {
    return kDifBadArg;
  }

  uint32_t enable_reg =
      mmio_region_read32(pwm->base_addr, PWM_PWM_EN_REG_OFFSET);
  *is_enabled =
      dif_bool_to_toggle(bitfield_bit32_read(enable_reg, channel_bit));

  return kDifOk;
}

dif_result_t dif_pwm_lock(const dif_pwm_t *pwm) {
  if (pwm == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(pwm->base_addr, PWM_REGWEN_REG_OFFSET, 0);

  return kDifOk;
}

dif_result_t dif_pwm_is_locked(const dif_pwm_t *pwm, bool *is_locked) {
  if (pwm == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked =
      mmio_region_read32(pwm->base_addr, PWM_REGWEN_REG_OFFSET) ? false : true;

  return kDifOk;
}
