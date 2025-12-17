// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/rv_timer.h"

#include "hw/top/dt/rv_timer.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"

#include "hw/top/rv_timer_regs.h"

static inline uint32_t rv_timer_reg_base(void) {
  return dt_rv_timer_primary_reg_block(kDtRvTimerFirst);
}

void rv_timer_init(void) {
  uint32_t prescaler = (uint32_t)kClockFreqPeripheralHz / 1000000 - 1;
  uint32_t cfg = RV_TIMER_CFG0_REG_RESVAL;
  cfg = bitfield_field32_write(cfg, RV_TIMER_CFG0_PRESCALE_FIELD, prescaler);
  const uint32_t kBase = rv_timer_reg_base();
  abs_mmio_write32(kBase + RV_TIMER_TIMER_V_LOWER0_REG_OFFSET, 0);
  abs_mmio_write32(kBase + RV_TIMER_TIMER_V_UPPER0_REG_OFFSET, 0);
  abs_mmio_write32(kBase + RV_TIMER_CFG0_REG_OFFSET, cfg);
  abs_mmio_write32(kBase + RV_TIMER_CTRL_REG_OFFSET, 1);
}

uint32_t rv_timer_get(void) {
  return abs_mmio_read32(rv_timer_reg_base() +
                         RV_TIMER_TIMER_V_LOWER0_REG_OFFSET);
}
