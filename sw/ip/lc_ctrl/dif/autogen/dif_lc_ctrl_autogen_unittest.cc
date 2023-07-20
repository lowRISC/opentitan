// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "lc_ctrl_regs.h"  // Generated.

namespace dif_lc_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class LcCtrlTest : public Test, public MmioTest {
 protected:
  dif_lc_ctrl_t lc_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public LcCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_lc_ctrl_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_lc_ctrl_init(dev().region(), &lc_ctrl_));
}

class AlertForceTest : public LcCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_lc_ctrl_alert_force(nullptr, kDifLcCtrlAlertFatalProgError));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_lc_ctrl_alert_force(nullptr, static_cast<dif_lc_ctrl_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(LC_CTRL_ALERT_TEST_REG_OFFSET,
                 {{LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_BIT, true}});
  EXPECT_DIF_OK(
      dif_lc_ctrl_alert_force(&lc_ctrl_, kDifLcCtrlAlertFatalProgError));

  // Force last alert.
  EXPECT_WRITE32(LC_CTRL_ALERT_TEST_REG_OFFSET,
                 {{LC_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_BIT, true}});
  EXPECT_DIF_OK(
      dif_lc_ctrl_alert_force(&lc_ctrl_, kDifLcCtrlAlertFatalBusIntegError));
}

}  // namespace
}  // namespace dif_lc_ctrl_autogen_unittest
