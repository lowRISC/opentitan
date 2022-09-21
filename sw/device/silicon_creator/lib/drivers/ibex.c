// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include "sw/device/lib/base/abs_mmio.h"
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
  uint32_t mask = matching_addr | ((size - 1) >> 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET, mask);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET, mask);

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
  uint32_t mask = matching_addr | ((size - 1) >> 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET, mask);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET, mask);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                   remap_addr);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                   remap_addr);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET, 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET, 1);
  icache_invalidate();
}
