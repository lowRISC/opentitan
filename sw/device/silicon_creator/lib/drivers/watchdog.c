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
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kWatchdogSecMmioInit,
                                  kWatchdogSecMmioConfigure);
  // Disable the watchdog bite when in test and RMA lifecycle states.
  hardened_bool_t enable = kHardenedBoolTrue;
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      enable = kHardenedBoolFalse;
      break;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      enable = kHardenedBoolTrue;
      break;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      enable = kHardenedBoolTrue;
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      enable = kHardenedBoolTrue;
      break;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      enable = kHardenedBoolFalse;
      break;
    default:
      HARDENED_TRAP();
  }

  uint32_t threshold = otp_read32(
      OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES_OFFSET);

  // Disable watchdog if `threshold` is less than minimum.
  if (launder32(threshold) < kWatchdogMinThreshold) {
    HARDENED_CHECK_LT(threshold, kWatchdogMinThreshold);
    enable = kHardenedBoolFalse;
  }

  watchdog_configure((watchdog_config_t){
      // 1.125 x bite_threshold
      .bark_threshold = (9 * threshold) / 8,
      .bite_threshold = threshold,
      .enable = enable,
  });
}

void watchdog_configure(watchdog_config_t config) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kWatchdogSecMmioConfigure, 4);
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
  abs_mmio_write32(kBase + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET,
                   config.bark_threshold);
  sec_mmio_write32(kBase + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                   config.bite_threshold);

  // Enable or disable the watchdog as requested.
  uint32_t ctrl = kCtrlEnable;
  switch (launder32(config.enable)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(config.enable, kHardenedBoolTrue);
      ctrl = kCtrlEnable;
      break;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(config.enable, kHardenedBoolFalse);
      ctrl = kCtrlDisable;
      break;
    default:
      HARDENED_TRAP();
  }
  sec_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, ctrl);

  // Redundantly re-request the pwrmgr configuration sync since it isn't
  // possible to use sec_mmio for it.
  abs_mmio_write32(kPwrMgrBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);
}

void watchdog_disable(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kWatchdogSecMmioDisable, 1);
  sec_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, kCtrlDisable);
}

void watchdog_pet(void) {
  abs_mmio_write32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
}

uint32_t watchdog_get(void) {
  return abs_mmio_read32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET);
}
