// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "pwrmgr_regs.h"

enum {
  kBase = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR,
  kPwrMgrBase = TOP_EARLGREY_PWRMGR_AON_BASE_ADDR,

  kCtrlEnable = 1 << AON_TIMER_WDOG_CTRL_ENABLE_BIT,
  kCtrlDisable = 0 << AON_TIMER_WDOG_CTRL_ENABLE_BIT,
};

void watchdog_init(lifecycle_state_t lc_state) {
  // Disable the watchdog bite when in test and RMA lifecycle states.
  hardened_bool_t enable = kHardenedBoolTrue;
  switch (lc_state) {
    case kLcStateTest:
      enable = kHardenedBoolFalse;
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      break;
    case kLcStateRma:
      enable = kHardenedBoolFalse;
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      break;
    default:
      break;
  }

  uint32_t threshold =
      otp_read32(OTP_CTRL_PARAM_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES_OFFSET);
  watchdog_configure(threshold, enable);
}

void watchdog_configure(uint32_t threshold, hardened_bool_t enable) {
  // Tell pwrmgr we want watchdog reset events to reset the chip.
  sec_mmio_write32(
      kPwrMgrBase + PWRMGR_RESET_EN_REG_OFFSET,
      bitfield_bit32_write(
          0, kTopEarlgreyPowerManagerResetRequestsAonTimerAonAonTimerRstReq,
          true));
  abs_mmio_write32(kPwrMgrBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);

  // Set the watchdog bite and bark thresholds.
  sec_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, kCtrlDisable);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, UINT32_MAX);
  sec_mmio_write32(kBase + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET, threshold);

  // Enable or disable the watchdog as requested.
  uint32_t ctrl = kCtrlEnable;
  if (enable == kHardenedBoolFalse) {
    ctrl = kCtrlDisable;
    HARDENED_CHECK_EQ(enable, kHardenedBoolFalse);
  }
  sec_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, ctrl);

  // Read back the control register to ensure it was set as expected.
  if ((abs_mmio_read32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET) & kCtrlEnable) !=
      kCtrlEnable) {
    HARDENED_CHECK_EQ(enable, kHardenedBoolFalse);
  }

  // Redundantly re-request the pwrmgr configuration sync since it isn't
  // possible to use sec_mmio for it.
  abs_mmio_write32(kPwrMgrBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);
}

void watchdog_disable(void) {
  sec_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, kCtrlDisable);
}

void watchdog_pet(void) {
  abs_mmio_write32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
}

uint32_t watchdog_get(void) {
  return abs_mmio_read32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET);
}
