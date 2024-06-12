// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

enum {
  kBase = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
};

uint32_t ibex_fpga_version(void) {
  return abs_mmio_read32(kBase + RV_CORE_IBEX_FPGA_INFO_REG_OFFSET);
}

void ibex_addr_remap_0_set(uint32_t matching_addr, uint32_t remap_addr,
                           size_t size) {
  // Work-around for opentitan#22884: Mask off bits below the alignment size
  // prior to programming the REMAP_ADDR register.
  size = size - 1;
  uint32_t match = (matching_addr & ~size) | size >> 1;
  remap_addr &= ~size;

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET, match);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET, match);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                   remap_addr);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                   remap_addr);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET, 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET, 1);
  icache_invalidate();
}

void ibex_addr_remap_1_set(uint32_t matching_addr, uint32_t remap_addr,
                           size_t size) {
  // Work-around for opentitan#22884: Mask off bits below the alignment size
  // prior to programming the REMAP_ADDR register.
  size = size - 1;
  uint32_t match = (matching_addr & ~size) | size >> 1;
  remap_addr &= ~size;

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET, match);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET, match);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                   remap_addr);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                   remap_addr);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET, 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET, 1);
  icache_invalidate();
}

uint32_t ibex_addr_remap_get(uint32_t index) {
  HARDENED_CHECK_LT(index, 2);
  index *= sizeof(uint32_t);
  if (abs_mmio_read32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + index)) {
    return abs_mmio_read32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET +
                           index);
  } else {
    return 0;
  }
}

void ibex_addr_remap_lockdown(uint32_t index) {
  HARDENED_CHECK_LT(index, 2);
  index *= sizeof(uint32_t);
  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET + index, 0);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET + index, 0);
}

// `extern` declarations to give the inline functions in the corresponding
// header a link location.
extern void ibex_mcycle_zero(void);
extern uint32_t ibex_mcycle32(void);
extern uint64_t ibex_mcycle(void);
extern uint64_t ibex_time_to_cycles(uint64_t time_us);
