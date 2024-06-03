// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rv_dm_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "rv_dm_regs.h"  // Generated.

namespace dif_rv_dm_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class RvDmTest : public Test, public MmioTest {
 protected:
  dif_rv_dm_t rv_dm_ = {.base_addr = dev().region()};
};

class InitTest : public RvDmTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_dm_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_rv_dm_init(dev().region(), &rv_dm_));
}

class AlertForceTest : public RvDmTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_dm_alert_force(nullptr, kDifRvDmAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_rv_dm_alert_force(nullptr, static_cast<dif_rv_dm_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(RV_DM_ALERT_TEST_REG_OFFSET,
                 {{RV_DM_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_rv_dm_alert_force(&rv_dm_, kDifRvDmAlertFatalFault));
}

}  // namespace
}  // namespace dif_rv_dm_autogen_unittest
