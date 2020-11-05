// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "pwrmgr_regs.h"  // Generated.

/**
 * Following static assertions make sure that generated values match the
 * definitions in the header, which we rely on for a simpler implementation.
 * These constants and their usages must be revisited if there is a change in
 * hardware.
 */

/**
 * Relevant bits of the control register must start at
 * `PWRMGR_CONTROL_CORE_CLK_EN_BIT` and be in the same order as
 * `dif_pwrmgr_domain_option_t` constants.
 */
_Static_assert(kDifPwrmgrDomainOptionCoreClockInLowPower ==
                   (1u << (PWRMGR_CONTROL_CORE_CLK_EN_BIT -
                           PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
               "Layout of control register changed.");

_Static_assert(kDifPwrmgrDomainOptionIoClockInLowPower ==
                   (1u << (PWRMGR_CONTROL_IO_CLK_EN_BIT -
                           PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
               "Layout of control register changed.");

_Static_assert(kDifPwrmgrDomainOptionUsbClockInLowPower ==
                   (1u << (PWRMGR_CONTROL_USB_CLK_EN_LP_BIT -
                           PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
               "Layout of control register changed.");

_Static_assert(kDifPwrmgrDomainOptionUsbClockInActivePower ==
                   (1u << (PWRMGR_CONTROL_USB_CLK_EN_ACTIVE_BIT -
                           PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
               "Layout of control register changed.");

_Static_assert(kDifPwrmgrDomainOptionMainPowerInLowPower ==
                   (1u << (PWRMGR_CONTROL_MAIN_PD_N_BIT -
                           PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
               "Layout of control register changed.");

/**
 * Bitfield for interpreting the configuration options in the control
 * register.
 */
static const bitfield_field32_t kDomainConfigBitfield = {
    .mask = kDifPwrmgrDomainOptionCoreClockInLowPower |
            kDifPwrmgrDomainOptionIoClockInLowPower |
            kDifPwrmgrDomainOptionUsbClockInLowPower |
            kDifPwrmgrDomainOptionUsbClockInActivePower |
            kDifPwrmgrDomainOptionMainPowerInLowPower,
    .index = PWRMGR_CONTROL_CORE_CLK_EN_BIT,
};

/**
 * Relevant bits of the WAKEUP_EN and WAKE_INFO registers must start at `0` and
 * be in the same order as `dif_pwrmgr_wakeup_request_source_t` constants.
 */
_Static_assert(kDifPwrmgrWakeupRequestSourceOne ==
                   (1u << PWRMGR_WAKEUP_EN_EN_0_BIT),
               "Layout of WAKEUP_EN register changed.");
_Static_assert(kDifPwrmgrWakeupRequestSourceOne ==
                   (1u << PWRMGR_WAKE_INFO_REASONS_BIT),
               "Layout of WAKE_INFO register changed.");

/**
 * Relevant bits of the RESET_EN register must start at `0` and be in the same
 * order as `dif_pwrmgr_reset_request_source_t` constants.
 */
_Static_assert(kDifPwrmgrResetRequestSourceOne ==
                   (1u << PWRMGR_RESET_EN_EN_0_BIT),
               "Layout of RESET_EN register changed.");

/**
 * `dif_pwrmgr_irq_t` constants must match the corresponding generated values.
 */
_Static_assert(kDifPwrmgrIrqWakeup == PWRMGR_INTR_COMMON_WAKEUP_BIT,
               "Layout of interrupt registers changed.");

/**
 * Register information for a request type.
 */
typedef struct request_reg_info {
  ptrdiff_t write_enable_reg_offset;
  bitfield_bit32_index_t write_enable_bit_index;
  ptrdiff_t sources_enable_reg_offset;
  ptrdiff_t cur_req_sources_reg_offset;
  bitfield_field32_t bitfield;
} request_reg_info_t;

/**
 * Register information for wakeup and reset requests.
 *
 * Wakeup and reset requests follow the same logic for configuration and
 * monitoring but use different registers. Defining these constants here
 * allows us to use the same code for both types of requests.
 */
static const request_reg_info_t request_reg_infos[2] = {
    [kDifPwrmgrReqTypeWakeup] =
        {
            .write_enable_reg_offset = PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET,
            .write_enable_bit_index = PWRMGR_WAKEUP_EN_REGWEN_EN_BIT,
            .sources_enable_reg_offset = PWRMGR_WAKEUP_EN_REG_OFFSET,
            .cur_req_sources_reg_offset = PWRMGR_WAKE_STATUS_REG_OFFSET,
            .bitfield =
                {
                    .mask = kDifPwrmgrWakeupRequestSourceOne,
                    .index = 0,
                },
        },
    [kDifPwrmgrReqTypeReset] =
        {
            .write_enable_reg_offset = PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
            .write_enable_bit_index = PWRMGR_RESET_EN_REGWEN_EN_BIT,
            .sources_enable_reg_offset = PWRMGR_RESET_EN_REG_OFFSET,
            .cur_req_sources_reg_offset = PWRMGR_RESET_STATUS_REG_OFFSET,
            .bitfield =
                {
                    .mask = kDifPwrmgrResetRequestSourceOne,
                    .index = 0,
                },
        },
};

/**
 * Checks if a value is a valid `dif_pwrmgr_toggle_t` and converts it to `bool`.
 */
DIF_WARN_UNUSED_RESULT
static bool toggle_to_bool(dif_pwrmgr_toggle_t val, bool *val_bool) {
  switch (val) {
    case kDifPwrmgrToggleEnabled:
      *val_bool = true;
      break;
    case kDifPwrmgrToggleDisabled:
      *val_bool = false;
      break;
    default:
      return false;
  }
  return true;
}

/**
 * Converts a `bool` to `dif_pwrmgr_toggle_t`.
 */
static dif_pwrmgr_toggle_t bool_to_toggle(bool val) {
  return val ? kDifPwrmgrToggleEnabled : kDifPwrmgrToggleDisabled;
}

/**
 * Checks if a value is a valid `dif_pwrmgr_req_type_t`.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_req_type(dif_pwrmgr_req_type_t val) {
  return val == kDifPwrmgrReqTypeWakeup || val == kDifPwrmgrReqTypeReset;
}

/**
 * Checks if a value is a valid `dif_pwrmgr_irq_t`.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_irq(dif_pwrmgr_irq_t val) {
  return val >= 0 && val <= kDifPwrmgrIrqLast;
}

/**
 * Checks if a value is valid for, i.e. fits in the mask of, a
 * `bitfield_field32_t`.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_for_bitfield(uint32_t val, bitfield_field32_t bitfield) {
  return (val & bitfield.mask) == val;
}

/**
 * Checks if the control register is locked.
 *
 * Control register is locked when low power is enabled and WFI occurs. It is
 * unlocked when the chip transitions back to active power state.
 */
DIF_WARN_UNUSED_RESULT
static bool control_register_is_locked(const dif_pwrmgr_t *pwrmgr) {
  // Control register is locked when `PWRMGR_CTRL_CFG_REGWEN_EN_BIT` bit is 0.
  return !bitfield_bit32_read(
      mmio_region_read32(pwrmgr->params.base_addr,
                         PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET),
      PWRMGR_CTRL_CFG_REGWEN_EN_BIT);
}

/**
 * The configuration registers CONTROL, WAKEUP_EN, and RESET_EN are all written
 * in the fast clock domain but used in the slow clock domain. Values of these
 * registers are not propagated across the clock boundary until this function is
 * called.
 */
static void sync_slow_clock_domain_polled(const dif_pwrmgr_t *pwrmgr) {
  // Start sync and wait for it to finish.
  mmio_region_write32(
      pwrmgr->params.base_addr, PWRMGR_CFG_CDC_SYNC_REG_OFFSET,
      bitfield_bit32_write(0, PWRMGR_CFG_CDC_SYNC_SYNC_BIT, true));
  while (bitfield_bit32_read(mmio_region_read32(pwrmgr->params.base_addr,
                                                PWRMGR_CFG_CDC_SYNC_REG_OFFSET),
                             PWRMGR_CFG_CDC_SYNC_SYNC_BIT)) {
  }
}

/**
 * Checks if sources of a request type are locked.
 */
DIF_WARN_UNUSED_RESULT
static bool request_sources_is_locked(const dif_pwrmgr_t *pwrmgr,
                                      dif_pwrmgr_req_type_t req_type) {
  request_reg_info_t reg_info = request_reg_infos[req_type];
  uint32_t reg_val = mmio_region_read32(pwrmgr->params.base_addr,
                                        reg_info.write_enable_reg_offset);
  // Locked if write enable bit is set to 0.
  return !bitfield_bit32_read(reg_val, reg_info.write_enable_bit_index);
}

dif_pwrmgr_result_t dif_pwrmgr_init(dif_pwrmgr_params_t params,
                                    dif_pwrmgr_t *pwrmgr) {
  if (pwrmgr == NULL) {
    return kDifPwrmgrBadArg;
  }

  *pwrmgr = (dif_pwrmgr_t){.params = params};

  return kDifPwrmgrOk;
}

dif_pwrmgr_config_result_t dif_pwrmgr_low_power_set_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t new_state) {
  if (pwrmgr == NULL) {
    return kDifPwrmgrConfigBadArg;
  }

  bool enable = false;
  if (!toggle_to_bool(new_state, &enable)) {
    return kDifPwrmgrConfigBadArg;
  }

  if (control_register_is_locked(pwrmgr)) {
    return kDifPwrMgrConfigLocked;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->params.base_addr, PWRMGR_CONTROL_REG_OFFSET);
  reg_val =
      bitfield_bit32_write(reg_val, PWRMGR_CONTROL_LOW_POWER_HINT_BIT, enable);
  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_CONTROL_REG_OFFSET,
                      reg_val);

  // Slow clock domain must be synced for changes to take effect.
  sync_slow_clock_domain_polled(pwrmgr);

  return kDifPwrmgrConfigOk;
}

dif_pwrmgr_result_t dif_pwrmgr_low_power_get_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t *cur_state) {
  if (pwrmgr == NULL || cur_state == NULL) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->params.base_addr, PWRMGR_CONTROL_REG_OFFSET);
  *cur_state = bool_to_toggle(
      bitfield_bit32_read(reg_val, PWRMGR_CONTROL_LOW_POWER_HINT_BIT));

  return kDifPwrmgrOk;
}

dif_pwrmgr_config_result_t dif_pwrmgr_set_domain_config(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_domain_config_t config) {
  if (pwrmgr == NULL || !is_valid_for_bitfield(config, kDomainConfigBitfield)) {
    return kDifPwrmgrConfigBadArg;
  }

  if (control_register_is_locked(pwrmgr)) {
    return kDifPwrMgrConfigLocked;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->params.base_addr, PWRMGR_CONTROL_REG_OFFSET);
  reg_val = bitfield_field32_write(reg_val, kDomainConfigBitfield, config);
  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_CONTROL_REG_OFFSET,
                      reg_val);

  // Slow clock domain must be synced for changes to take effect.
  sync_slow_clock_domain_polled(pwrmgr);

  return kDifPwrmgrConfigOk;
}

dif_pwrmgr_result_t dif_pwrmgr_get_domain_config(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_domain_config_t *config) {
  if (pwrmgr == NULL || config == NULL) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->params.base_addr, PWRMGR_CONTROL_REG_OFFSET);
  *config = bitfield_field32_read(reg_val, kDomainConfigBitfield);

  return kDifPwrmgrOk;
}

dif_pwrmgr_config_result_t dif_pwrmgr_set_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t sources) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type)) {
    return kDifPwrmgrConfigBadArg;
  }

  request_reg_info_t reg_info = request_reg_infos[req_type];

  if (!is_valid_for_bitfield(sources, reg_info.bitfield)) {
    return kDifPwrmgrConfigBadArg;
  }

  // Return early if locked.
  if (request_sources_is_locked(pwrmgr, req_type)) {
    return kDifPwrMgrConfigLocked;
  }

  // Write new value
  uint32_t reg_val = bitfield_field32_write(0, reg_info.bitfield, sources);
  mmio_region_write32(pwrmgr->params.base_addr,
                      reg_info.sources_enable_reg_offset, reg_val);
  // Slow clock domain must be synced for changes to take effect.
  sync_slow_clock_domain_polled(pwrmgr);

  return kDifPwrmgrConfigOk;
}

dif_pwrmgr_result_t dif_pwrmgr_get_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) || sources == NULL) {
    return kDifPwrmgrBadArg;
  }

  request_reg_info_t reg_info = request_reg_infos[req_type];
  uint32_t reg_val = mmio_region_read32(pwrmgr->params.base_addr,
                                        reg_info.sources_enable_reg_offset);
  *sources = bitfield_field32_read(reg_val, reg_info.bitfield);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_get_current_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) || sources == NULL) {
    return kDifPwrmgrBadArg;
  }

  request_reg_info_t reg_info = request_reg_infos[req_type];
  uint32_t reg_val = mmio_region_read32(pwrmgr->params.base_addr,
                                        reg_info.cur_req_sources_reg_offset);
  *sources = bitfield_field32_read(reg_val, reg_info.bitfield);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_request_sources_lock(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type)) {
    return kDifPwrmgrBadArg;
  }

  // Only a single bit of this register is significant, thus we don't perform a
  // read-modify-write. Setting this bit to 0 locks sources.
  mmio_region_write32(pwrmgr->params.base_addr,
                      request_reg_infos[req_type].write_enable_reg_offset, 0);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_request_sources_is_locked(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    bool *is_locked) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) || is_locked == NULL) {
    return kDifPwrmgrBadArg;
  }

  *is_locked = request_sources_is_locked(pwrmgr, req_type);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_wakeup_request_recording_set_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t new_state) {
  if (pwrmgr == NULL) {
    return kDifPwrmgrBadArg;
  }

  bool enable = false;
  if (!toggle_to_bool(new_state, &enable)) {
    return kDifPwrmgrBadArg;
  }

  // Only a single bit of this register is significant, thus we don't perform a
  // read-modify-write. Setting this bit to 1 disables recording.
  uint32_t reg_val =
      bitfield_bit32_write(0, PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT, !enable);

  mmio_region_write32(pwrmgr->params.base_addr,
                      PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET, reg_val);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_wakeup_request_recording_get_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t *cur_state) {
  if (pwrmgr == NULL || cur_state == NULL) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(
      pwrmgr->params.base_addr, PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET);
  // Recording is disabled if this bit is set to 1.
  *cur_state = bool_to_toggle(
      !bitfield_bit32_read(reg_val, PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT));

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_wakeup_reason_get(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_wakeup_reason_t *reason) {
  if (pwrmgr == NULL || reason == NULL) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->params.base_addr, PWRMGR_WAKE_INFO_REG_OFFSET);

  dif_pwrmgr_wakeup_types_t types = 0;
  if (bitfield_bit32_read(reg_val, PWRMGR_WAKE_INFO_FALL_THROUGH_BIT)) {
    types |= kDifPwrmgrWakeupTypeFallThrough;
  }
  if (bitfield_bit32_read(reg_val, PWRMGR_WAKE_INFO_ABORT_BIT)) {
    types |= kDifPwrmgrWakeupTypeAbort;
  }

  uint32_t request_sources = bitfield_field32_read(
      reg_val, request_reg_infos[kDifPwrmgrReqTypeWakeup].bitfield);
  if (request_sources != 0) {
    types |= kDifPwrmgrWakeupTypeRequest;
  }

  *reason = (dif_pwrmgr_wakeup_reason_t){
      .types = types,
      .request_sources = request_sources,
  };

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_wakeup_reason_clear(const dif_pwrmgr_t *pwrmgr) {
  if (pwrmgr == NULL) {
    return kDifPwrmgrBadArg;
  }

  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_WAKE_INFO_REG_OFFSET,
                      UINT32_MAX);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_is_pending(const dif_pwrmgr_t *pwrmgr,
                                              dif_pwrmgr_irq_t irq,
                                              bool *is_pending) {
  if (pwrmgr == NULL || !is_valid_irq(irq) || is_pending == NULL) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(pwrmgr->params.base_addr,
                                        PWRMGR_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg_val, irq);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_acknowledge(const dif_pwrmgr_t *pwrmgr,
                                               dif_pwrmgr_irq_t irq) {
  if (pwrmgr == NULL || !is_valid_irq(irq)) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val = bitfield_bit32_write(0, irq, true);
  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_INTR_STATE_REG_OFFSET,
                      reg_val);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_get_enabled(const dif_pwrmgr_t *pwrmgr,
                                               dif_pwrmgr_irq_t irq,
                                               dif_pwrmgr_toggle_t *state) {
  if (pwrmgr == NULL || !is_valid_irq(irq) || state == NULL) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(pwrmgr->params.base_addr,
                                        PWRMGR_INTR_ENABLE_REG_OFFSET);
  *state = bool_to_toggle(bitfield_bit32_read(reg_val, irq));

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_set_enabled(const dif_pwrmgr_t *pwrmgr,
                                               dif_pwrmgr_irq_t irq,
                                               dif_pwrmgr_toggle_t state) {
  if (pwrmgr == NULL || !is_valid_irq(irq)) {
    return kDifPwrmgrBadArg;
  }

  bool enable = false;
  if (!toggle_to_bool(state, &enable)) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(pwrmgr->params.base_addr,
                                        PWRMGR_INTR_ENABLE_REG_OFFSET);
  reg_val = bitfield_bit32_write(reg_val, irq, enable);
  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_INTR_ENABLE_REG_OFFSET,
                      reg_val);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_force(const dif_pwrmgr_t *pwrmgr,
                                         dif_pwrmgr_irq_t irq) {
  if (pwrmgr == NULL || !is_valid_irq(irq)) {
    return kDifPwrmgrBadArg;
  }

  uint32_t reg_val = bitfield_bit32_write(0, irq, true);
  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_INTR_TEST_REG_OFFSET,
                      reg_val);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_disable_all(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_irq_snapshot_t *snapshot) {
  if (pwrmgr == NULL) {
    return kDifPwrmgrBadArg;
  }

  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(pwrmgr->params.base_addr,
                                   PWRMGR_INTR_ENABLE_REG_OFFSET);
  }
  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_INTR_ENABLE_REG_OFFSET,
                      0);

  return kDifPwrmgrOk;
}

dif_pwrmgr_result_t dif_pwrmgr_irq_restore_all(
    const dif_pwrmgr_t *pwrmgr, const dif_pwrmgr_irq_snapshot_t *snapshot) {
  if (pwrmgr == NULL || snapshot == NULL) {
    return kDifPwrmgrBadArg;
  }

  mmio_region_write32(pwrmgr->params.base_addr, PWRMGR_INTR_ENABLE_REG_OFFSET,
                      *snapshot);
  return kDifPwrmgrOk;
}
