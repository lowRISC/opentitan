// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_sram_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "sram_ctrl_regs.h"  // Generated.

namespace dif_sram_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SramCtrlTest : public Test, public MmioTest {
 protected:
  dif_sram_ctrl_t sram_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public SramCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_sram_ctrl_init(dev().region(), &sram_ctrl_), kDifOk);
}

class AlertForceTest : public SramCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_alert_force(nullptr, kDifSramCtrlAlertFatalError),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(dif_sram_ctrl_alert_force(nullptr,
                                      static_cast<dif_sram_ctrl_alert_t>(32)),
            kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SRAM_CTRL_ALERT_TEST_REG_OFFSET,
                 {{SRAM_CTRL_ALERT_TEST_FATAL_ERROR_BIT, true}});
  EXPECT_EQ(dif_sram_ctrl_alert_force(&sram_ctrl_, kDifSramCtrlAlertFatalError),
            kDifOk);
}

}  // namespace
}  // namespace dif_sram_ctrl_autogen_unittest
