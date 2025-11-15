// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pwrmgr.h"

#include "hw/top/dt/dt_aon_timer.h"
#include "hw/top/dt/dt_api.h"
#include "hw/top/dt/dt_pwrmgr.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/pwrmgr_regs.h"

static inline uint32_t pwrmgr_base(void) {
  return dt_pwrmgr_primary_reg_block(kDtPwrmgrAon);
}

enum {
  kSyncConfig = (1 << PWRMGR_CFG_CDC_SYNC_SYNC_BIT),
};

/**
 * A power manager request type.
 */
typedef enum pwrmgr_req_type {
  kPwrmgrReqTypeWakeup,
  kPwrmgrReqTypeReset,
} pwr_mgr_req_type_t;

/**
 * Obtain a bit index of wakeup/reset request for a device and a signal.
 *
 * Given a module instance (identified by its instance ID) and a wakeup
 * or reset request index from this module, return the source bit index
 * that, once shifted into a bitmask, can be programmed into the pwrmgr
 * `RESET_EN` register.
 *
 * @param req_type Request type (wake up or reset request).
 * @param inst_id A DT instance ID.
 * @param signal_idx Signal index.
 * @param[out] source_idx The source index corresponding to the wakeup or reset
 * requested.
 * @return `kErrorOk` if a signal matches, or a `kErrorPwrmgr` error otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t pwrmgr_find_request_source(pwr_mgr_req_type_t req_type,
                                       dt_instance_id_t inst_id,
                                       size_t signal_idx, size_t *source_idx) {
  dt_pwrmgr_t dt = kDtPwrmgrAon;

  if (req_type == kPwrmgrReqTypeWakeup) {
    for (size_t idx = 0; idx < dt_pwrmgr_wakeup_src_count(dt); idx++) {
      dt_pwrmgr_wakeup_src_t src = dt_pwrmgr_wakeup_src(dt, idx);
      if (src.inst_id == inst_id && src.wakeup == signal_idx) {
        *source_idx = idx;
        return kErrorOk;
      }
    }
    return kErrorPwrmgrUnknownRequestSource;
  } else if (req_type == kPwrmgrReqTypeReset) {
    for (size_t idx = 0; idx < dt_pwrmgr_reset_request_src_count(dt); idx++) {
      dt_pwrmgr_reset_req_src_t src = dt_pwrmgr_reset_request_src(dt, idx);
      if (src.inst_id == inst_id && src.reset_req == signal_idx) {
        *source_idx = idx;
        return kErrorOk;
      }
    }
    return kErrorPwrmgrUnknownRequestSource;
  } else {
    return kErrorPwrmgrInvalidRequestType;
  }
}

void pwrmgr_enable_watchdog_reset_request(void) {
  uint32_t pwrmgr_base = dt_pwrmgr_primary_reg_block(kDtPwrmgrAon);
  uint32_t enabled_resets = 0;
  size_t reset_source = 0;

  // Tell pwrmgr we want watchdog reset events to reset the chip.
  HARDENED_CHECK_EQ(
      pwrmgr_find_request_source(kPwrmgrReqTypeReset,
                                 dt_aon_timer_instance_id(kDtAonTimerAon),
                                 kDtAonTimerResetReqAonTimer, &reset_source),
      kErrorOk);
  enabled_resets = bitfield_bit32_write(0, reset_source, true);
  sec_mmio_write32(pwrmgr_base + PWRMGR_RESET_EN_REG_OFFSET, enabled_resets);
  pwrmgr_cdc_sync(1);
}

void pwrmgr_cdc_sync(uint32_t n) {
  // We want to timeout if the CDC bit doesn't self clear.  It should take
  // approximately 4 AON ticks to complete.  We wait 25% longer (5 ticks).
  uint32_t cpu_cycle_timeout =
      (uint32_t)kClockFreqCpuHz / (uint32_t)kClockFreqAonHz * 5;

  // Ensure the bit is clear before requesting another sync.
  ibex_mcycle_zero();
  while (abs_mmio_read32(pwrmgr_base() + PWRMGR_CFG_CDC_SYNC_REG_OFFSET)) {
    if (ibex_mcycle32() > cpu_cycle_timeout) {
      // If the sync bit isn't clear, we shouldn't set it again.  Abort.
      return;
    }
  }
  // Perform the sync procedure the requested number of times.
  while (n--) {
    ibex_mcycle_zero();
    abs_mmio_write32(pwrmgr_base() + PWRMGR_CFG_CDC_SYNC_REG_OFFSET,
                     kSyncConfig);
    while (abs_mmio_read32(pwrmgr_base() + PWRMGR_CFG_CDC_SYNC_REG_OFFSET)) {
      if (ibex_mcycle32() > cpu_cycle_timeout)
        // If the sync bit isn't clear, we shouldn't set it again.  Abort.
        return;
    }
  }
}

void pwrmgr_all_resets_enable(void) {
  uint32_t reset_src_count = dt_pwrmgr_reset_request_src_count(kDtPwrmgrAon);
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kPwrmgrSecMmioAllResetsEnable, 1);
  // Enable all resets.
  sec_mmio_write32(pwrmgr_base() + PWRMGR_RESET_EN_REG_OFFSET, reset_src_count);
  pwrmgr_cdc_sync(1);
}
