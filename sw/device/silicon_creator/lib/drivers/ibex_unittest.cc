// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/lib/sw/device/base/mock_abs_mmio.h"
#include "sw/lib/sw/device/silicon_creator/base/mock_sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "rv_core_ibex_regs.h"

namespace ibex_unittest {
namespace {

class AddressTranslationTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR;
  rom_test::MockSecMmio sec_;
};

TEST_F(AddressTranslationTest, SlotCount) {
  EXPECT_EQ(ibex_addr_remap_slots(), RV_CORE_IBEX_PARAM_NUM_REGIONS);
}

TEST_F(AddressTranslationTest, Slot0Success) {
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

  EXPECT_EQ(ibex_addr_remap_set(0, matching_addr, remap_addr, size), kErrorOk);
}

TEST_F(AddressTranslationTest, SlotMaxSuccess) {
  uint32_t matching_addr = 0xB040000;
  uint32_t remap_addr = 0x6000000;
  uint32_t size = 0x80000;
  size_t slot = ibex_addr_remap_slots() - 1;
  uint32_t offset = slot * 4;

  EXPECT_SEC_WRITE32(
      base_ + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET + offset, 0xb07ffff);
  EXPECT_SEC_WRITE32(
      base_ + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET + offset, 0xb07ffff);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET + offset,
                     remap_addr);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET + offset,
                     remap_addr);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + offset,
                     1);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET + offset,
                     1);

  EXPECT_EQ(ibex_addr_remap_set(slot, matching_addr, remap_addr, size),
            kErrorOk);
}

TEST_F(AddressTranslationTest, SlotInvalidFail) {
  uint32_t slot = ibex_addr_remap_slots();

  EXPECT_EQ(ibex_addr_remap_set(slot, 0, 0, 0), kErrorIbexBadRemapSlot);
}

TEST_F(AddressTranslationTest, Slot0LockSuccess) {
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 1);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 1);

  EXPECT_EQ(ibex_addr_remap_lock(0), kErrorOk);
}

TEST_F(AddressTranslationTest, SlotMaxLockSuccess) {
  size_t slot = ibex_addr_remap_slots() - 1;
  uint32_t offset = slot * 4;

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET + offset, 1);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET + offset, 1);

  EXPECT_EQ(ibex_addr_remap_lock(slot), kErrorOk);
}

TEST_F(AddressTranslationTest, SlotInvalidLockFail) {
  uint32_t slot = ibex_addr_remap_slots();

  EXPECT_EQ(ibex_addr_remap_lock(slot), kErrorIbexBadRemapSlot);
}

}  // namespace
}  // namespace ibex_unittest
