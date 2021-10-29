// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_rom_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "rom_ctrl_regs.h"  // Generated.

namespace dif_rom_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class RomCtrlTest : public Test, public MmioTest {
 protected:
  dif_rom_ctrl_t rom_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public RomCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_rom_ctrl_init({.base_addr = dev().region()}, nullptr),
            kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_rom_ctrl_init({.base_addr = dev().region()}, &rom_ctrl_),
            kDifOk);
}

class AlertForceTest : public RomCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_rom_ctrl_alert_force(nullptr, kDifRomCtrlAlertFatal),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(
      dif_rom_ctrl_alert_force(nullptr, static_cast<dif_rom_ctrl_alert_t>(32)),
      kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(ROM_CTRL_ALERT_TEST_REG_OFFSET,
                 {{ROM_CTRL_ALERT_TEST_FATAL_BIT, true}});
  EXPECT_EQ(dif_rom_ctrl_alert_force(&rom_ctrl_, kDifRomCtrlAlertFatal),
            kDifOk);
}

}  // namespace
}  // namespace dif_rom_ctrl_autogen_unittest
