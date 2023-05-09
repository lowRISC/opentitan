// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_adc_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"

#include "adc_ctrl_regs.h"  // Generated.

static_assert(ADC_CTRL_PARAM_NUM_ADC_CHANNEL == 2,
              "Expected two ADC Controller channels.");
static_assert(ADC_CTRL_PARAM_NUM_ADC_FILTER == 8,
              "Expected eight ADC Controller filters.");
static_assert(ADC_CTRL_ADC_CHN0_FILTER_CTL_MIN_V_FIELD_WIDTH == 10,
              "Expected channel-0 filter min-voltage field to be 10 bits.");
static_assert(ADC_CTRL_ADC_CHN1_FILTER_CTL_MIN_V_FIELD_WIDTH == 10,
              "Expected channel-1 filter min-voltage field to be 10 bits.");
static_assert(ADC_CTRL_ADC_CHN0_FILTER_CTL_MAX_V_FIELD_WIDTH == 10,
              "Expected channel-0 filter max-voltage field to be 10 bits.");
static_assert(ADC_CTRL_ADC_CHN1_FILTER_CTL_MAX_V_FIELD_WIDTH == 10,
              "Expected channel-1 filter max-voltage field to be 10 bits.");

dif_result_t dif_adc_ctrl_configure(const dif_adc_ctrl_t *adc_ctrl,
                                    dif_adc_ctrl_config_t config) {
  if (adc_ctrl == NULL ||
      config.power_up_time_aon_cycles > ADC_CTRL_ADC_PD_CTL_PWRUP_TIME_MASK ||
      config.wake_up_time_aon_cycles > ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_MASK ||
      config.num_low_power_samples == 0 ||
      config.num_normal_power_samples == 0) {
    return kDifBadArg;
  }

  uint32_t en_ctrl_reg = ADC_CTRL_ADC_EN_CTL_REG_RESVAL;
  uint32_t pd_ctrl_reg = ADC_CTRL_ADC_PD_CTL_REG_RESVAL;
  uint32_t lp_sample_ctrl_reg = ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_RESVAL;
  uint32_t np_sample_ctrl_reg = ADC_CTRL_ADC_SAMPLE_CTL_REG_RESVAL;

  switch (config.mode) {
    case kDifAdcCtrlLowPowerScanMode:
      pd_ctrl_reg = bitfield_bit32_write(pd_ctrl_reg,
                                         ADC_CTRL_ADC_PD_CTL_LP_MODE_BIT, true);
      pd_ctrl_reg = bitfield_field32_write(
          pd_ctrl_reg, ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_FIELD,
          config.wake_up_time_aon_cycles);
      lp_sample_ctrl_reg = bitfield_field32_write(
          lp_sample_ctrl_reg, ADC_CTRL_ADC_LP_SAMPLE_CTL_LP_SAMPLE_CNT_FIELD,
          config.num_low_power_samples);
      OT_FALLTHROUGH_INTENDED;
    case kDifAdcCtrlNormalPowerScanMode:
      np_sample_ctrl_reg = bitfield_field32_write(
          np_sample_ctrl_reg, ADC_CTRL_ADC_SAMPLE_CTL_NP_SAMPLE_CNT_FIELD,
          config.num_normal_power_samples);
      break;
    case kDifAdcCtrlOneshotMode:
      en_ctrl_reg = bitfield_bit32_write(
          en_ctrl_reg, ADC_CTRL_ADC_EN_CTL_ONESHOT_MODE_BIT, true);
      break;
    default:
      return kDifBadArg;
  }

  // Regardless of the mode, the ADC could be powered down, so we need to set
  // the power-up time.
  pd_ctrl_reg =
      bitfield_field32_write(pd_ctrl_reg, ADC_CTRL_ADC_PD_CTL_PWRUP_TIME_FIELD,
                             config.power_up_time_aon_cycles);
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                      en_ctrl_reg);
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_PD_CTL_REG_OFFSET,
                      pd_ctrl_reg);
  mmio_region_write32(adc_ctrl->base_addr,
                      ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_OFFSET,
                      lp_sample_ctrl_reg);
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET,
                      np_sample_ctrl_reg);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_configure_filter(const dif_adc_ctrl_t *adc_ctrl,
                                           dif_adc_ctrl_channel_t channel,
                                           dif_adc_ctrl_filter_config_t config,
                                           dif_toggle_t enabled) {
  if (adc_ctrl == NULL || config.min_voltage > 1023 ||
      config.max_voltage > 1023) {
    return kDifBadArg;
  }

  ptrdiff_t filter_ctrl_reg_offset;
  bitfield_field32_t min_voltage_field;
  bitfield_field32_t max_voltage_field;
  bitfield_bit32_index_t in_range_bit;
  bitfield_bit32_index_t enable_bit;

#define DIF_ADC_CTRL_CHANNEL0_FILTER_CONFIG_CASE_(filter_)                    \
  case kDifAdcCtrlFilter##filter_:                                            \
    filter_ctrl_reg_offset =                                                  \
        ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_REG_OFFSET;                  \
    min_voltage_field =                                                       \
        ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_MIN_V_##filter_##_FIELD;     \
    max_voltage_field =                                                       \
        ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_MAX_V_##filter_##_FIELD;     \
    in_range_bit =                                                            \
        ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_COND_##filter_##_BIT;        \
    enable_bit = ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_EN_##filter_##_BIT; \
    break;

#define DIF_ADC_CTRL_CHANNEL1_FILTER_CONFIG_CASE_(filter_)                    \
  case kDifAdcCtrlFilter##filter_:                                            \
    filter_ctrl_reg_offset =                                                  \
        ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_REG_OFFSET;                  \
    min_voltage_field =                                                       \
        ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_MIN_V_##filter_##_FIELD;     \
    max_voltage_field =                                                       \
        ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_MAX_V_##filter_##_FIELD;     \
    in_range_bit =                                                            \
        ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_COND_##filter_##_BIT;        \
    enable_bit = ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_EN_##filter_##_BIT; \
    break;

  switch (channel) {
    case kDifAdcCtrlChannel0:
      switch (config.filter) {
        DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_CHANNEL0_FILTER_CONFIG_CASE_)
        default:
          return kDifBadArg;
      }
      break;
    case kDifAdcCtrlChannel1:
      switch (config.filter) {
        DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_CHANNEL1_FILTER_CONFIG_CASE_)
        default:
          return kDifBadArg;
      }
      break;
    default:
      return kDifBadArg;
  }

#undef DIF_ADC_CTRL_CHANNEL0_FILTER_CONFIG_CASE_
#undef DIF_ADC_CTRL_CHANNEL1_FILTER_CONFIG_CASE_

  // Configure filter control register.
  uint32_t filter_ctrl_reg =
      bitfield_field32_write(0, min_voltage_field, config.min_voltage);
  filter_ctrl_reg = bitfield_field32_write(filter_ctrl_reg, max_voltage_field,
                                           config.max_voltage);
  filter_ctrl_reg =
      bitfield_bit32_write(filter_ctrl_reg, in_range_bit, !config.in_range);
  filter_ctrl_reg = bitfield_bit32_write(filter_ctrl_reg, enable_bit,
                                         dif_toggle_to_bool(enabled));
  mmio_region_write32(adc_ctrl->base_addr, filter_ctrl_reg_offset,
                      filter_ctrl_reg);

  // Configure wakeup control register.
  uint32_t wakeup_ctrl_reg = mmio_region_read32(
      adc_ctrl->base_addr, ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET);
  wakeup_ctrl_reg = bitfield_bit32_write(wakeup_ctrl_reg, config.filter,
                                         config.generate_wakeup_on_match);
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET,
                      wakeup_ctrl_reg);

  // Configure interrupt control register.
  uint32_t intr_ctrl_reg =
      mmio_region_read32(adc_ctrl->base_addr, ADC_CTRL_ADC_INTR_CTL_REG_OFFSET);
  intr_ctrl_reg = bitfield_bit32_write(intr_ctrl_reg, config.filter,
                                       config.generate_irq_on_match);
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_INTR_CTL_REG_OFFSET,
                      intr_ctrl_reg);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_set_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                      dif_toggle_t enabled) {
  if (adc_ctrl == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  uint32_t en_ctrl_reg =
      mmio_region_read32(adc_ctrl->base_addr, ADC_CTRL_ADC_EN_CTL_REG_OFFSET);
  en_ctrl_reg =
      bitfield_bit32_write(en_ctrl_reg, ADC_CTRL_ADC_EN_CTL_ADC_ENABLE_BIT,
                           dif_toggle_to_bool(enabled));
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                      en_ctrl_reg);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_get_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                      dif_toggle_t *is_enabled) {
  if (adc_ctrl == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t en_ctrl_reg =
      mmio_region_read32(adc_ctrl->base_addr, ADC_CTRL_ADC_EN_CTL_REG_OFFSET);
  *is_enabled = dif_bool_to_toggle(
      bitfield_bit32_read(en_ctrl_reg, ADC_CTRL_ADC_EN_CTL_ADC_ENABLE_BIT));

  return kDifOk;
}

static bool get_filter_offset(dif_adc_ctrl_channel_t channel,
                              dif_adc_ctrl_filter_t filter,
                              ptrdiff_t *filter_ctrl_reg_offset) {
#define DIF_ADC_CTRL_CHANNEL0_FILTER_CTRL_REG_CASE_(filter_) \
  case kDifAdcCtrlFilter##filter_:                           \
    *filter_ctrl_reg_offset =                                \
        ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_REG_OFFSET; \
    break;

#define DIF_ADC_CTRL_CHANNEL1_FILTER_CTRL_REG_CASE_(filter_) \
  case kDifAdcCtrlFilter##filter_:                           \
    *filter_ctrl_reg_offset =                                \
        ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_REG_OFFSET; \
    break;

  switch (channel) {
    case kDifAdcCtrlChannel0:
      switch (filter) {
        DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_CHANNEL0_FILTER_CTRL_REG_CASE_)
        default:
          return false;
      }
      break;
    case kDifAdcCtrlChannel1:
      switch (filter) {
        DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_CHANNEL1_FILTER_CTRL_REG_CASE_)
        default:
          return false;
      }
      break;
    default:
      return false;
  }

#undef DIF_ADC_CTRL_CHANNEL0_FILTER_CTRL_REG_CASE_
#undef DIF_ADC_CTRL_CHANNEL1_FILTER_CTRL_REG_CASE_

  return true;
}

static bool get_filter_enable_bit(dif_adc_ctrl_channel_t channel,
                                  dif_adc_ctrl_filter_t filter,
                                  bitfield_bit32_index_t *enable_bit) {
#define DIF_ADC_CTRL_CHANNEL0_FILTER_ENABLE_CASE_(filter_)                     \
  case kDifAdcCtrlFilter##filter_:                                             \
    *enable_bit = ADC_CTRL_ADC_CHN0_FILTER_CTL_##filter_##_EN_##filter_##_BIT; \
    break;

#define DIF_ADC_CTRL_CHANNEL1_FILTER_ENABLE_CASE_(filter_)                     \
  case kDifAdcCtrlFilter##filter_:                                             \
    *enable_bit = ADC_CTRL_ADC_CHN1_FILTER_CTL_##filter_##_EN_##filter_##_BIT; \
    break;

  switch (channel) {
    case kDifAdcCtrlChannel0:
      switch (filter) {
        DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_CHANNEL0_FILTER_ENABLE_CASE_)
        default:
          return false;
      }
      break;
    case kDifAdcCtrlChannel1:
      switch (filter) {
        DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_CHANNEL1_FILTER_ENABLE_CASE_)
        default:
          return false;
      }
      break;
    default:
      return false;
  }

#undef DIF_ADC_CTRL_CHANNEL0_FILTER_ENABLE_CASE_
#undef DIF_ADC_CTRL_CHANNEL1_FILTER_ENABLE_CASE_

  return true;
}

dif_result_t dif_adc_ctrl_filter_set_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                             dif_adc_ctrl_channel_t channel,
                                             dif_adc_ctrl_filter_t filter,
                                             dif_toggle_t enabled) {
  if (adc_ctrl == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  ptrdiff_t filter_ctrl_reg_offset;
  bitfield_bit32_index_t enable_bit;
  if (!get_filter_offset(channel, filter, &filter_ctrl_reg_offset)) {
    return kDifBadArg;
  }
  if (!get_filter_enable_bit(channel, filter, &enable_bit)) {
    return kDifBadArg;
  }

  uint32_t filter_ctrl_reg =
      mmio_region_read32(adc_ctrl->base_addr, filter_ctrl_reg_offset);
  filter_ctrl_reg = bitfield_bit32_write(filter_ctrl_reg, enable_bit,
                                         dif_toggle_to_bool(enabled));
  mmio_region_write32(adc_ctrl->base_addr, filter_ctrl_reg_offset,
                      filter_ctrl_reg);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_filter_get_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                             dif_adc_ctrl_channel_t channel,
                                             dif_adc_ctrl_filter_t filter,
                                             dif_toggle_t *is_enabled) {
  if (adc_ctrl == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t filter_ctrl_reg_offset;
  bitfield_bit32_index_t enable_bit;
  if (!get_filter_offset(channel, filter, &filter_ctrl_reg_offset)) {
    return kDifBadArg;
  }
  if (!get_filter_enable_bit(channel, filter, &enable_bit)) {
    return kDifBadArg;
  }

  uint32_t filter_ctrl_reg =
      mmio_region_read32(adc_ctrl->base_addr, filter_ctrl_reg_offset);
  *is_enabled =
      dif_bool_to_toggle(bitfield_bit32_read(filter_ctrl_reg, enable_bit));

  return kDifOk;
}

dif_result_t dif_adc_ctrl_get_triggered_value(const dif_adc_ctrl_t *adc_ctrl,
                                              dif_adc_ctrl_channel_t channel,
                                              uint16_t *value) {
  if (adc_ctrl == NULL || value == NULL) {
    return kDifBadArg;
  }

  uint32_t value_reg;

#define DIF_ADC_CTRL_CHANNEL_TRIG_VALUE_CASE_(channel_)                           \
  case kDifAdcCtrlChannel##channel_:                                              \
    value_reg = mmio_region_read32(                                               \
        adc_ctrl->base_addr, ADC_CTRL_ADC_CHN_VAL_##channel_##_REG_OFFSET);       \
    *value = (uint16_t)bitfield_field32_read(                                     \
        value_reg,                                                                \
        ADC_CTRL_ADC_CHN_VAL_##channel_##_ADC_CHN_VALUE_INTR_##channel_##_FIELD); \
    break;

  switch (channel) {
    DIF_ADC_CTRL_CHANNEL_LIST(DIF_ADC_CTRL_CHANNEL_TRIG_VALUE_CASE_)
    default:
      return kDifBadArg;
  }

#undef DIF_ADC_CTRL_CHANNEL_TRIG_VALUE_CASE_

  return kDifOk;
}

dif_result_t dif_adc_ctrl_get_latest_value(const dif_adc_ctrl_t *adc_ctrl,
                                           dif_adc_ctrl_channel_t channel,
                                           uint16_t *value) {
  if (adc_ctrl == NULL || value == NULL) {
    return kDifBadArg;
  }

  uint32_t value_reg;

#define DIF_ADC_CTRL_CHANNEL_LATEST_VALUE_CASE_(channel_)                    \
  case kDifAdcCtrlChannel##channel_:                                         \
    value_reg = mmio_region_read32(                                          \
        adc_ctrl->base_addr, ADC_CTRL_ADC_CHN_VAL_##channel_##_REG_OFFSET);  \
    *value = (uint16_t)bitfield_field32_read(                                \
        value_reg,                                                           \
        ADC_CTRL_ADC_CHN_VAL_##channel_##_ADC_CHN_VALUE_##channel_##_FIELD); \
    break;

  switch (channel) {
    DIF_ADC_CTRL_CHANNEL_LIST(DIF_ADC_CTRL_CHANNEL_LATEST_VALUE_CASE_)
    default:
      return kDifBadArg;
  }

#undef DIF_ADC_CTRL_CHANNEL_LATEST_VALUE_CASE_

  return kDifOk;
}

dif_result_t dif_adc_ctrl_reset(const dif_adc_ctrl_t *adc_ctrl) {
  if (adc_ctrl == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_FSM_RST_REG_OFFSET, 1);
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_FSM_RST_REG_OFFSET, 0);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_irq_get_causes(const dif_adc_ctrl_t *adc_ctrl,
                                         uint32_t *causes) {
  if (adc_ctrl == NULL || causes == NULL) {
    return kDifBadArg;
  }

  *causes = mmio_region_read32(adc_ctrl->base_addr,
                               ADC_CTRL_ADC_INTR_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_irq_clear_causes(const dif_adc_ctrl_t *adc_ctrl,
                                           uint32_t causes) {
  if (adc_ctrl == NULL || causes > kDifAdcCtrlIrqCauseAll) {
    return kDifBadArg;
  }

  uint32_t filter_causes = (~(uint32_t)kDifAdcCtrlIrqCauseOneshot) & causes;
  if (filter_causes) {
    mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_FILTER_STATUS_REG_OFFSET,
                        filter_causes);
  }

  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_INTR_STATUS_REG_OFFSET,
                      causes);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_filter_match_wakeup_set_enabled(
    const dif_adc_ctrl_t *adc_ctrl, dif_adc_ctrl_filter_t filter,
    dif_toggle_t enabled) {
  if (adc_ctrl == NULL || filter >= ADC_CTRL_PARAM_NUM_ADC_FILTER ||
      !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  uint32_t wakeup_ctrl_reg = mmio_region_read32(
      adc_ctrl->base_addr, ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET);
  wakeup_ctrl_reg = bitfield_bit32_write(wakeup_ctrl_reg, filter,
                                         dif_toggle_to_bool(enabled));
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET,
                      wakeup_ctrl_reg);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_filter_match_wakeup_get_enabled(
    const dif_adc_ctrl_t *adc_ctrl, dif_adc_ctrl_filter_t filter,
    dif_toggle_t *is_enabled) {
  if (adc_ctrl == NULL || filter >= ADC_CTRL_PARAM_NUM_ADC_FILTER ||
      is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t wakeup_ctrl_reg = mmio_region_read32(
      adc_ctrl->base_addr, ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET);
  *is_enabled =
      dif_bool_to_toggle(bitfield_bit32_read(wakeup_ctrl_reg, filter));

  return kDifOk;
}

dif_result_t dif_adc_ctrl_irq_cause_set_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                                uint32_t causes,
                                                dif_toggle_t enabled) {
  if (adc_ctrl == NULL || causes > kDifAdcCtrlIrqCauseAll ||
      !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  uint32_t enabled_causes =
      mmio_region_read32(adc_ctrl->base_addr, ADC_CTRL_ADC_INTR_CTL_REG_OFFSET);
  if (enabled == kDifToggleDisabled) {
    enabled_causes &= ~causes;
  } else {
    enabled_causes |= causes;
  }
  mmio_region_write32(adc_ctrl->base_addr, ADC_CTRL_ADC_INTR_CTL_REG_OFFSET,
                      enabled_causes);

  return kDifOk;
}

dif_result_t dif_adc_ctrl_irq_cause_get_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                                uint32_t *enabled_causes) {
  if (adc_ctrl == NULL || enabled_causes == NULL) {
    return kDifBadArg;
  }

  *enabled_causes =
      mmio_region_read32(adc_ctrl->base_addr, ADC_CTRL_ADC_INTR_CTL_REG_OFFSET);

  return kDifOk;
}
