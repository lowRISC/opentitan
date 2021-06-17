// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum { kBase = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR };

#define AON_TIMER_RATE 200000

void watchdog_init(uint32_t timeout_ms) {
  abs_mmio_write32(kBase + AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
  abs_mmio_write32(kBase + AON_TIMER_WKUP_THOLD_REG_OFFSET, 0xFFFFFFFF);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, 0xFFFFFFFF);
  abs_mmio_write32(kBase + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                   timeout_ms * (AON_TIMER_RATE / 1000));
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
