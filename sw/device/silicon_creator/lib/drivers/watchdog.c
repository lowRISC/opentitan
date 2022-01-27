// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

#include "sw/device/lib/base/abs_mmio.h"

#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"

enum {
  kBase = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR,
  kPwrMgrBase = TOP_EARLGREY_PWRMGR_AON_BASE_ADDR,
  // The AON domain is always clocked at 200 Hz.
  // TODO(lowRISC/opentitan#7385): update this after the AON frequency is
  // formally defined in the project.
  kAonTimerRate = 200000,
};

void watchdog_init(uint32_t timeout_ms) {
  // Tell pwrmgr we want watchdog reset events to reset the chip.
  abs_mmio_write32(
      kPwrMgrBase + PWRMGR_RESET_EN_REG_OFFSET,
      bitfield_bit32_write(
          0, kTopEarlgreyPowerManagerResetRequestsAonTimerAonAonTimerRstReq,
          true));
  abs_mmio_write32(kPwrMgrBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);

  // Disable the watchdog before reconfiguring it.
  abs_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  // Configure the watchdog to bite at the requested timeout.
  abs_mmio_write32(kBase + AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WKUP_THOLD_REG_OFFSET, UINT32_MAX);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, UINT32_MAX);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                   timeout_ms * (kAonTimerRate / 1000));
  if (timeout_ms) {
    abs_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, 1);
  }
}

void watchdog_pet(void) {
  abs_mmio_write32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
}

uint32_t watchdog_get(void) {
  return abs_mmio_read32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET);
}
