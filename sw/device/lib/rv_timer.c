// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/rv_timer.h"

#include "rv_timer_regs.h"  // Generated.
#include "sw/device/lib/common.h"
#include "sw/device/lib/runtime/ibex.h"

#define RV_TIMER0_BASE_ADDR 0x40080000
#define HART_CFG_ADDR_GAP 0x100

static const uint32_t NS_IN_S = 1000 * 1000 * 1000;

void rv_timer_set_us_tick(uint32_t hart) {
  uint32_t ticks_per_us = (uint32_t)((1000 * kIbexClockFreqHz) / NS_IN_S) - 1;

  REG32(RV_TIMER_CFG0(0) + hart * 4) =
      (ticks_per_us & RV_TIMER_CFG0_PRESCALE_MASK) |
      (1 << RV_TIMER_CFG0_STEP_OFFSET);
}

void rv_timer_set_cmp(uint32_t hart, uint64_t cmp) {
  REG32(RV_TIMER_COMPARE_UPPER0_0(0) + hart * HART_CFG_ADDR_GAP) = -1;
  REG32(RV_TIMER_COMPARE_LOWER0_0(0) + hart * HART_CFG_ADDR_GAP) =
      (uint32_t)cmp;
  REG32(RV_TIMER_COMPARE_UPPER0_0(0) + hart * HART_CFG_ADDR_GAP) =
      (uint32_t)(cmp >> 32);
}

void rv_timer_ctrl(uint32_t hart, bool en) {
  REG32(RV_TIMER_CTRL(0)) = (en) ? SETBIT(REG32(RV_TIMER_CTRL(0)), hart)
                                 : CLRBIT(REG32(RV_TIMER_CTRL(0)), hart);
}

void rv_timer_intr_enable(uint32_t hart, bool en) {
  REG32(RV_TIMER_INTR_ENABLE0(0)) =
      (en) ? SETBIT(REG32(RV_TIMER_INTR_ENABLE0(0)), hart)
           : CLRBIT(REG32(RV_TIMER_INTR_ENABLE0(0)), hart);
}

void rv_timer_clr_all_intrs(void) {
  REG32(RV_TIMER_INTR_STATE0(0)) = REG32(RV_TIMER_INTR_STATE0(0));
}
