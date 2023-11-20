// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/runtime/hart.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "rv_core_ibex_regs.h"

enum {
  kBase = TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR,
};

static_assert(RV_CORE_IBEX_IBUS_ADDR_MATCHING_MULTIREG_COUNT ==
                  RV_CORE_IBEX_PARAM_NUM_REGIONS,
              "Number of IBUS remapper registers must match number of regions");
static_assert(RV_CORE_IBEX_DBUS_ADDR_MATCHING_MULTIREG_COUNT ==
                  RV_CORE_IBEX_PARAM_NUM_REGIONS,
              "Number of DBUS remapper registers must match number of regions");

uint32_t ibex_fpga_version(void) {
  return abs_mmio_read32(kBase + RV_CORE_IBEX_FPGA_INFO_REG_OFFSET);
}

unsigned ibex_addr_remap_slots(void) { return RV_CORE_IBEX_PARAM_NUM_REGIONS; }

rom_error_t ibex_addr_remap_set(size_t slot, uint32_t matching_addr,
                                uint32_t remap_addr, size_t size) {
  if (slot >= RV_CORE_IBEX_PARAM_NUM_REGIONS) {
    return kErrorIbexBadRemapSlot;
  }
  slot *= 4;

  uint32_t mask = matching_addr | ((size - 1) >> 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET + slot,
                   mask);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET + slot,
                   mask);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET + slot,
                   remap_addr);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET + slot,
                   remap_addr);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + slot, 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET + slot, 1);
  icache_invalidate();

  return kErrorOk;
}

rom_error_t ibex_addr_remap_lock(size_t slot) {
  if (slot >= RV_CORE_IBEX_PARAM_NUM_REGIONS) {
    return kErrorIbexBadRemapSlot;
  }
  slot *= 4;

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET + slot, 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET + slot, 1);

  return kErrorOk;
}
