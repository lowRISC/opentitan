// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rom_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

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
  EXPECT_DIF_BADARG(dif_rom_ctrl_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_rom_ctrl_init(dev().region(), &rom_ctrl_));
}

class AlertForceTest : public RomCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rom_ctrl_alert_force(nullptr, kDifRomCtrlAlertFatal));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_rom_ctrl_alert_force(nullptr, static_cast<dif_rom_ctrl_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(ROM_CTRL_ALERT_TEST_REG_OFFSET,
                 {{ROM_CTRL_ALERT_TEST_FATAL_BIT, true}});
  EXPECT_DIF_OK(dif_rom_ctrl_alert_force(&rom_ctrl_, kDifRomCtrlAlertFatal));
}

}  // namespace
}  // namespace dif_rom_ctrl_autogen_unittest
