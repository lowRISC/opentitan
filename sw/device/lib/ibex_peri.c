// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/ibex_peri.h"

#include "sw/device/lib/base/mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

struct ibex_address_translation_regs {
  uint32_t ibus_addr_maching;
  uint32_t ibus_addr_remap;
  uint32_t ibus_addr_en;
  uint32_t dbus_addr_maching;
  uint32_t dbus_addr_remap;
  uint32_t dbus_addr_en;
};
static const struct ibex_address_translation_regs
    kRegs_map[ibex_simple_address_translation_id_count] = {
        [ibex_simple_address_translation_id_0] =
            {
                .ibus_addr_maching =
                    RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET,
                .ibus_addr_remap = RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                .ibus_addr_en = RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET,
                .dbus_addr_maching =
                    RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET,
                .dbus_addr_remap = RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                .dbus_addr_en = RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET,
            },
        [ibex_simple_address_translation_id_1] =
            {
                .ibus_addr_maching =
                    RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET,
                .ibus_addr_remap = RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                .ibus_addr_en = RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET,
                .dbus_addr_maching =
                    RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET,
                .dbus_addr_remap = RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                .dbus_addr_en = RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET,
            },
};

void init_translation(uint32_t src_addr, uint32_t size, uint32_t dst_addr) {
  ibex_set_translation(ibex_simple_address_translation_id_0, src_addr, size,
                       dst_addr);
}

int ibex_set_translation(ibex_simple_address_translation_idx idx,
                          uint32_t virtual_addr, uint32_t size,
                          uint32_t physical_addr) {
  if (idx >= ibex_simple_address_translation_id_count) {
    return -1;
  }

  struct ibex_address_translation_regs regs = kRegs_map[idx];

  mmio_region_t ibex_base =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  uint32_t mask = virtual_addr | ((size - 1) >> 1);
  mmio_region_write32(ibex_base, regs.ibus_addr_maching, mask);
  mmio_region_write32(ibex_base, regs.dbus_addr_maching, mask);

  mmio_region_write32(ibex_base, regs.ibus_addr_remap, physical_addr);
  mmio_region_write32(ibex_base, regs.dbus_addr_remap, physical_addr);

  mmio_region_write32(ibex_base, regs.ibus_addr_en, 1);
  mmio_region_write32(ibex_base, regs.dbus_addr_en, 1);
  return 0;
}
