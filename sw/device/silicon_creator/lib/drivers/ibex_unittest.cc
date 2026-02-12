// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top/rv_core_ibex_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace ibex_unittest {
namespace {

class IbexTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR;
  rom_test::MockSecMmio sec_;
  rom_test::MockAbsMmio mmio_;
};

class AddressTranslationTest : public IbexTest {};

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

  ibex_addr_remap_set(0, matching_addr, remap_addr, size);
}

TEST_F(AddressTranslationTest, Slot1Sucess) {
  // Note: 0xB040_0000 is not power-of-two aligned with respect to the size.
  // The remap function will force-align the matching_addr to the size.
  uint32_t matching_addr = 0xB040000;
  uint32_t remap_addr = 0x6000000;
  uint32_t size = 0x80000;
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET,
                     0xb03ffff);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET,
                     0xb03ffff);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                     remap_addr);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                     remap_addr);

  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET, 1);
  EXPECT_SEC_WRITE32(base_ + RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET, 1);

  ibex_addr_remap_set(1, matching_addr, remap_addr, size);
}

class NmiEnableTest : public IbexTest {};

TEST_F(NmiEnableTest, AllNmis) {
  // Enable alert NMIs.
  EXPECT_ABS_WRITE32(base_ + RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET, 1);
  ibex_enable_nmi(kIbexNmiSourceAlert);

  // Enable watchdog NMIs.
  EXPECT_ABS_WRITE32(base_ + RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET, 2);
  ibex_enable_nmi(kIbexNmiSourceWdog);

  // Enable all NMIs.
  EXPECT_ABS_WRITE32(base_ + RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET, 3);
  ibex_enable_nmi(kIbexNmiSourceAll);
}

class NmiClearTest : public IbexTest {};

TEST_F(NmiClearTest, AllNmis) {
  // Clear alert NMIs.
  EXPECT_ABS_WRITE32(base_ + RV_CORE_IBEX_NMI_STATE_REG_OFFSET, 1);
  ibex_clear_nmi(kIbexNmiSourceAlert);

  // Clear watchdog NMIs.
  EXPECT_ABS_WRITE32(base_ + RV_CORE_IBEX_NMI_STATE_REG_OFFSET, 2);
  ibex_clear_nmi(kIbexNmiSourceWdog);

  // Clear all NMIs.
  EXPECT_ABS_WRITE32(base_ + RV_CORE_IBEX_NMI_STATE_REG_OFFSET, 3);
  ibex_clear_nmi(kIbexNmiSourceAll);
}

}  // namespace
}  // namespace ibex_unittest
