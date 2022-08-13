// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

namespace ibex_unittest {
namespace {

class AddressTranslationTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR;
  rom_test::MockSecMmio sec_;
};

TEST_F(AddressTranslationTest, Slot0Sucess) {
  uint32_t matching_addr = 0x9000000;
  uint32_t remap_addr = 0x2000000;
  uint32_t size = 0x8000;
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET,
                     0x9003fff);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET,
                     0x9003fff);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                     remap_addr);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                     remap_addr);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET, 1);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET, 1);

  ibex_addr_remap_0_set(matching_addr, remap_addr, size);
}

TEST_F(AddressTranslationTest, Slot1Sucess) {
  uint32_t matching_addr = 0xB040000;
  uint32_t remap_addr = 0x6000000;
  uint32_t size = 0x80000;
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET,
                     0xb07ffff);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET,
                     0xb07ffff);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                     remap_addr);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                     remap_addr);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET, 1);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET, 1);

  ibex_addr_remap_1_set(matching_addr, remap_addr, size);
}
}  // namespace
}  // namespace ibex_unittest
