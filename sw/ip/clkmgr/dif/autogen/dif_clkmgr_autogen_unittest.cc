// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_clkmgr_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "clkmgr_regs.h"  // Generated.

namespace dif_clkmgr_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class ClkmgrTest : public Test, public MmioTest {
 protected:
  dif_clkmgr_t clkmgr_ = {.base_addr = dev().region()};
};

class InitTest : public ClkmgrTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_clkmgr_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_clkmgr_init(dev().region(), &clkmgr_));
}

class AlertForceTest : public ClkmgrTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_clkmgr_alert_force(nullptr, kDifClkmgrAlertRecovFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_clkmgr_alert_force(nullptr, static_cast<dif_clkmgr_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(CLKMGR_ALERT_TEST_REG_OFFSET,
                 {{CLKMGR_ALERT_TEST_RECOV_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_clkmgr_alert_force(&clkmgr_, kDifClkmgrAlertRecovFault));

  // Force last alert.
  EXPECT_WRITE32(CLKMGR_ALERT_TEST_REG_OFFSET,
                 {{CLKMGR_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_clkmgr_alert_force(&clkmgr_, kDifClkmgrAlertFatalFault));
}

}  // namespace
}  // namespace dif_clkmgr_autogen_unittest
