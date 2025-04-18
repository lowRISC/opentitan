// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

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
static_assert(kDifPwrmgrDomainOptionCoreClockInLowPower ==
                  (1u << (PWRMGR_CONTROL_CORE_CLK_EN_BIT -
                          PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
              "Layout of control register changed.");

static_assert(kDifPwrmgrDomainOptionIoClockInLowPower ==
                  (1u << (PWRMGR_CONTROL_IO_CLK_EN_BIT -
                          PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
              "Layout of control register changed.");

#if defined(OPENTITAN_IS_EARLGREY)
static_assert(kDifPwrmgrDomainOptionUsbClockInLowPower ==
                  (1u << (PWRMGR_CONTROL_USB_CLK_EN_LP_BIT -
                          PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
              "Layout of control register changed.");

static_assert(kDifPwrmgrDomainOptionUsbClockInActivePower ==
                  (1u << (PWRMGR_CONTROL_USB_CLK_EN_ACTIVE_BIT -
                          PWRMGR_CONTROL_CORE_CLK_EN_BIT)),
              "Layout of control register changed.");
#endif /* OPENTITAN_IS */

static_assert(kDifPwrmgrDomainOptionMainPowerInLowPower ==
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
#if defined(OPENTITAN_IS_EARLGREY)
            kDifPwrmgrDomainOptionUsbClockInLowPower |
            kDifPwrmgrDomainOptionUsbClockInActivePower |
#elif defined(OPENTITAN_IS_DARJEELING)
/* Darjeeling has no USB clock. */
#else
#error "dif_pwrmgr does not support this top"
#endif
            kDifPwrmgrDomainOptionMainPowerInLowPower,
    .index = PWRMGR_CONTROL_CORE_CLK_EN_BIT,
};

/**
 * `dif_pwrmgr_irq_t` constants must match the corresponding generated values.
 */
static_assert(kDifPwrmgrIrqWakeup == PWRMGR_INTR_COMMON_WAKEUP_BIT,
              "Layout of interrupt registers changed.");

/**
 * Register information for a request type.
 */
typedef struct request_reg_info {
  ptrdiff_t write_enable_reg_offset;
  bitfield_bit32_index_t write_enable_bit_index;
  ptrdiff_t sources_enable_reg_offset;
  ptrdiff_t cur_req_sources_reg_offset;
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
        },
    [kDifPwrmgrReqTypeReset] =
        {
            .write_enable_reg_offset = PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
            .write_enable_bit_index = PWRMGR_RESET_EN_REGWEN_EN_BIT,
            .sources_enable_reg_offset = PWRMGR_RESET_EN_REG_OFFSET,
            .cur_req_sources_reg_offset = PWRMGR_RESET_STATUS_REG_OFFSET,
        },
};

dif_result_t dif_pwrmgr_find_request_source(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dt_instance_id_t inst_id, size_t sig_idx,
    dif_pwrmgr_request_sources_t *sources) {
  if (pwrmgr == NULL || sources == NULL) {
    return kDifBadArg;
  }
  dt_pwrmgr_t dt;
  DIF_RETURN_IF_ERROR(dif_pwrmgr_get_dt(pwrmgr, &dt));
  // Query the DT to find the information.
  if (req_type == kDifPwrmgrReqTypeWakeup) {
    for (size_t i = 0; i < dt_pwrmgr_wakeup_src_count(dt); i++) {
      dt_pwrmgr_wakeup_src_t src = dt_pwrmgr_wakeup_src(dt, i);
      if (src.inst_id == inst_id && src.wakeup == sig_idx) {
        *sources = 1u << i;
        return kDifOk;
      }
    }
    return kDifError;
  } else if (req_type == kDifPwrmgrReqTypeReset) {
    for (size_t i = 0; i < dt_pwrmgr_reset_request_src_count(dt); i++) {
      dt_pwrmgr_reset_req_src_t src = dt_pwrmgr_reset_request_src(dt, i);
      if (src.inst_id == inst_id && src.reset_req == sig_idx) {
        *sources = 1u << i;
        return kDifOk;
      }
    }
    return kDifError;
  } else {
    return kDifBadArg;
  }
}

/**
 * Obtain the bitfield in PWRMGR_{WAKEUP,RESET}_EN_REG_OFFSET which
 * represents all wakeup/reset sources.
 */
OT_WARN_UNUSED_RESULT
static dif_result_t request_reg_bitfield(const dif_pwrmgr_t *pwrmgr,
                                         dif_pwrmgr_req_type_t req_type,
                                         bitfield_field32_t *bitfield) {
  dt_pwrmgr_t dt;
  dif_result_t res = dif_pwrmgr_get_dt(pwrmgr, &dt);
  if (res != kDifOk) {
    return res;
  }

  size_t count = 0;
  if (req_type == kDifPwrmgrReqTypeWakeup) {
    count = dt_pwrmgr_wakeup_src_count(dt);
  } else if (req_type == kDifPwrmgrReqTypeReset) {
    count = dt_pwrmgr_reset_request_src_count(dt);
  } else {
    return kDifBadArg;
  }
  bitfield->index = 0;
  bitfield->mask = (1 << count) - 1;
  return kDifOk;
}

dif_result_t dif_pwrmgr_get_all_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources) {
  bitfield_field32_t bitfield;
  dif_result_t res = request_reg_bitfield(pwrmgr, req_type, &bitfield);
  if (res == kDifOk) {
    *sources = bitfield.mask;
  }
  return res;
}

/**
 * Checks if a value is a valid `dif_pwrmgr_req_type_t`.
 */
OT_WARN_UNUSED_RESULT
static bool is_valid_req_type(dif_pwrmgr_req_type_t val) {
  return val == kDifPwrmgrReqTypeWakeup || val == kDifPwrmgrReqTypeReset;
}

/**
 * Checks if a value is valid for, i.e. fits in the mask of, a
 * `bitfield_field32_t`.
 */
OT_WARN_UNUSED_RESULT
static bool is_valid_for_bitfield(uint32_t val, bitfield_field32_t bitfield) {
  return (val & bitfield.mask) == val;
}

/**
 * Checks if the control register is locked.
 *
 * Control register is locked when low power is enabled and WFI occurs. It is
 * unlocked when the chip transitions back to active power state.
 */
OT_WARN_UNUSED_RESULT
static bool control_register_is_locked(const dif_pwrmgr_t *pwrmgr) {
  // Control register is locked when `PWRMGR_CTRL_CFG_REGWEN_EN_BIT` bit is 0.
  return !bitfield_bit32_read(
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET),
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
      pwrmgr->base_addr, PWRMGR_CFG_CDC_SYNC_REG_OFFSET,
      bitfield_bit32_write(0, PWRMGR_CFG_CDC_SYNC_SYNC_BIT, true));
  while (bitfield_bit32_read(
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CFG_CDC_SYNC_REG_OFFSET),
      PWRMGR_CFG_CDC_SYNC_SYNC_BIT)) {
  }
}

/**
 * Checks if sources of a request type are locked.
 */
OT_WARN_UNUSED_RESULT
static bool request_sources_is_locked(const dif_pwrmgr_t *pwrmgr,
                                      dif_pwrmgr_req_type_t req_type) {
  request_reg_info_t reg_info = request_reg_infos[req_type];
  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, reg_info.write_enable_reg_offset);
  // Locked if write enable bit is set to 0.
  return !bitfield_bit32_read(reg_val, reg_info.write_enable_bit_index);
}

dif_result_t dif_pwrmgr_low_power_set_enabled(const dif_pwrmgr_t *pwrmgr,
                                              dif_toggle_t new_state,
                                              dif_toggle_t sync_state) {
  if (pwrmgr == NULL || !dif_is_valid_toggle(new_state) ||
      !dif_is_valid_toggle(sync_state)) {
    return kDifBadArg;
  }

  if (control_register_is_locked(pwrmgr)) {
    return kDifLocked;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CONTROL_REG_OFFSET);
  reg_val = bitfield_bit32_write(reg_val, PWRMGR_CONTROL_LOW_POWER_HINT_BIT,
                                 dif_toggle_to_bool(new_state));
  mmio_region_write32(pwrmgr->base_addr, PWRMGR_CONTROL_REG_OFFSET, reg_val);

  // Slow clock domain may be synced for changes to take effect.
  if (sync_state == kDifToggleEnabled)
    sync_slow_clock_domain_polled(pwrmgr);

  return kDifOk;
}

dif_result_t dif_pwrmgr_low_power_get_enabled(const dif_pwrmgr_t *pwrmgr,
                                              dif_toggle_t *cur_state) {
  if (pwrmgr == NULL || cur_state == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CONTROL_REG_OFFSET);
  *cur_state = dif_bool_to_toggle(
      bitfield_bit32_read(reg_val, PWRMGR_CONTROL_LOW_POWER_HINT_BIT));

  return kDifOk;
}

dif_result_t dif_pwrmgr_set_domain_config(const dif_pwrmgr_t *pwrmgr,
                                          dif_pwrmgr_domain_config_t config,
                                          dif_toggle_t sync_state) {
  if (pwrmgr == NULL || !is_valid_for_bitfield(config, kDomainConfigBitfield) ||
      !dif_is_valid_toggle(sync_state)) {
    return kDifBadArg;
  }

  if (control_register_is_locked(pwrmgr)) {
    return kDifLocked;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CONTROL_REG_OFFSET);
  reg_val = bitfield_field32_write(reg_val, kDomainConfigBitfield, config);
  mmio_region_write32(pwrmgr->base_addr, PWRMGR_CONTROL_REG_OFFSET, reg_val);

  // Slow clock domain must be synced for changes to take effect.
  if (sync_state == kDifToggleEnabled)
    sync_slow_clock_domain_polled(pwrmgr);

  return kDifOk;
}

dif_result_t dif_pwrmgr_get_domain_config(const dif_pwrmgr_t *pwrmgr,
                                          dif_pwrmgr_domain_config_t *config) {
  if (pwrmgr == NULL || config == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CONTROL_REG_OFFSET);
  *config = (dif_pwrmgr_domain_config_t)bitfield_field32_read(
      reg_val, kDomainConfigBitfield);

  return kDifOk;
}

dif_result_t dif_pwrmgr_set_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t sources, dif_toggle_t sync_state) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) ||
      !dif_is_valid_toggle(sync_state)) {
    return kDifBadArg;
  }

  request_reg_info_t reg_info = request_reg_infos[req_type];
  bitfield_field32_t bitfield;
  DIF_RETURN_IF_ERROR(request_reg_bitfield(pwrmgr, req_type, &bitfield));

  if (!is_valid_for_bitfield(sources, bitfield)) {
    return kDifBadArg;
  }

  // Return early if locked.
  if (request_sources_is_locked(pwrmgr, req_type)) {
    return kDifLocked;
  }

  // Write new value
  uint32_t reg_val = bitfield_field32_write(0, bitfield, sources);
  mmio_region_write32(pwrmgr->base_addr, reg_info.sources_enable_reg_offset,
                      reg_val);
  // Slow clock domain may be synced for changes to take effect.
  if (sync_state == kDifToggleEnabled)
    sync_slow_clock_domain_polled(pwrmgr);

  return kDifOk;
}

dif_result_t dif_pwrmgr_get_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) || sources == NULL) {
    return kDifBadArg;
  }

  request_reg_info_t reg_info = request_reg_infos[req_type];
  bitfield_field32_t bitfield;
  dif_result_t res = request_reg_bitfield(pwrmgr, req_type, &bitfield);
  if (res != kDifOk) {
    return res;
  }
  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, reg_info.sources_enable_reg_offset);
  *sources = bitfield_field32_read(reg_val, bitfield);

  return kDifOk;
}

dif_result_t dif_pwrmgr_get_current_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) || sources == NULL) {
    return kDifBadArg;
  }

  request_reg_info_t reg_info = request_reg_infos[req_type];
  bitfield_field32_t bitfield;
  dif_result_t res = request_reg_bitfield(pwrmgr, req_type, &bitfield);
  if (res != kDifOk) {
    return res;
  }
  uint32_t reg_val = mmio_region_read32(pwrmgr->base_addr,
                                        reg_info.cur_req_sources_reg_offset);
  *sources = bitfield_field32_read(reg_val, bitfield);

  return kDifOk;
}

dif_result_t dif_pwrmgr_request_sources_lock(const dif_pwrmgr_t *pwrmgr,
                                             dif_pwrmgr_req_type_t req_type) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type)) {
    return kDifBadArg;
  }

  // Only a single bit of this register is significant, thus we don't perform a
  // read-modify-write. Setting this bit to 0 locks sources.
  mmio_region_write32(pwrmgr->base_addr,
                      request_reg_infos[req_type].write_enable_reg_offset, 0);

  return kDifOk;
}

dif_result_t dif_pwrmgr_request_sources_is_locked(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    bool *is_locked) {
  if (pwrmgr == NULL || !is_valid_req_type(req_type) || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = request_sources_is_locked(pwrmgr, req_type);

  return kDifOk;
}

dif_result_t dif_pwrmgr_wakeup_request_recording_set_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_toggle_t new_state) {
  if (pwrmgr == NULL || !dif_is_valid_toggle(new_state)) {
    return kDifBadArg;
  }

  // Only a single bit of this register is significant, thus we don't perform a
  // read-modify-write. Setting this bit to 1 disables recording.
  uint32_t reg_val = bitfield_bit32_write(
      0, PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT, !dif_toggle_to_bool(new_state));
  mmio_region_write32(pwrmgr->base_addr,
                      PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET, reg_val);

  return kDifOk;
}

dif_result_t dif_pwrmgr_wakeup_request_recording_get_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_toggle_t *cur_state) {
  if (pwrmgr == NULL || cur_state == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val = mmio_region_read32(
      pwrmgr->base_addr, PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET);
  // Recording is disabled if this bit is set to 1.
  *cur_state = dif_bool_to_toggle(
      !bitfield_bit32_read(reg_val, PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT));

  return kDifOk;
}

dif_result_t dif_pwrmgr_wakeup_reason_get(const dif_pwrmgr_t *pwrmgr,
                                          dif_pwrmgr_wakeup_reason_t *reason) {
  if (pwrmgr == NULL || reason == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_WAKE_INFO_REG_OFFSET);

  dif_pwrmgr_wakeup_types_t types = 0;
  if (bitfield_bit32_read(reg_val, PWRMGR_WAKE_INFO_FALL_THROUGH_BIT)) {
    types |= kDifPwrmgrWakeupTypeFallThrough;
  }
  if (bitfield_bit32_read(reg_val, PWRMGR_WAKE_INFO_ABORT_BIT)) {
    types |= kDifPwrmgrWakeupTypeAbort;
  }

  bitfield_field32_t bitfield;
  dif_result_t res =
      request_reg_bitfield(pwrmgr, kDifPwrmgrReqTypeWakeup, &bitfield);
  if (res != kDifOk) {
    return res;
  }
  uint32_t request_sources = bitfield_field32_read(reg_val, bitfield);
  if (request_sources != 0) {
    types |= kDifPwrmgrWakeupTypeRequest;
  }

  *reason = (dif_pwrmgr_wakeup_reason_t){
      .types = types,
      .request_sources = request_sources,
  };

  return kDifOk;
}

dif_result_t dif_pwrmgr_wakeup_reason_clear(const dif_pwrmgr_t *pwrmgr) {
  if (pwrmgr == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(pwrmgr->base_addr, PWRMGR_WAKE_INFO_REG_OFFSET,
                      UINT32_MAX);

  return kDifOk;
}

dif_result_t dif_pwrmgr_fatal_err_code_get_codes(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_fatal_err_codes_t *codes) {
  if (pwrmgr == NULL || codes == NULL) {
    return kDifBadArg;
  }
  *codes =
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_FAULT_STATUS_REG_OFFSET);
  return kDifOk;
}
