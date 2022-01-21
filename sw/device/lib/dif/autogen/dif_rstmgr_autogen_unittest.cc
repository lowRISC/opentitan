// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rstmgr_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "rstmgr_regs.h"  // Generated.

namespace dif_rstmgr_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class RstmgrTest : public Test, public MmioTest {
 protected:
  dif_rstmgr_t rstmgr_ = {.base_addr = dev().region()};
};

class InitTest : public RstmgrTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_rstmgr_init(dev().region(), &rstmgr_), kDifOk);
}

class AlertForceTest : public RstmgrTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_alert_force(nullptr, kDifRstmgrAlertFatalFault),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(
      dif_rstmgr_alert_force(nullptr, static_cast<dif_rstmgr_alert_t>(32)),
      kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(RSTMGR_ALERT_TEST_REG_OFFSET,
                 {{RSTMGR_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_EQ(dif_rstmgr_alert_force(&rstmgr_, kDifRstmgrAlertFatalFault),
            kDifOk);
}

}  // namespace
}  // namespace dif_rstmgr_autogen_unittest
