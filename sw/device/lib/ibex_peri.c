// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/ibex_peri.h"

#include "sw/device/lib/base/mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

void init_translation(uint32_t src_addr, uint32_t size, uint32_t dst_addr) {
  mmio_region_t ibex_base =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  uint32_t mask = src_addr | ((size - 1) >> 1);
  mmio_region_write32(ibex_base, RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET,
                      mask);
  mmio_region_write32(ibex_base, RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET,
                      mask);

  mmio_region_write32(ibex_base, RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                      dst_addr);
  mmio_region_write32(ibex_base, RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                      dst_addr);

  mmio_region_write32(ibex_base, RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET, 1);
  mmio_region_write32(ibex_base, RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET, 1);
}

uint32_t fpga_version(void) {
  mmio_region_t ibex_base =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  return mmio_region_read32(ibex_base, RV_CORE_IBEX_FPGA_INFO_REG_OFFSET);
}
