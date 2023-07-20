// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rv_core_ibex_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "rv_core_ibex_regs.h"  // Generated.

namespace dif_rv_core_ibex_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class RvCoreIbexTest : public Test, public MmioTest {
 protected:
  dif_rv_core_ibex_t rv_core_ibex_ = {.base_addr = dev().region()};
};

class InitTest : public RvCoreIbexTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_core_ibex_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_rv_core_ibex_init(dev().region(), &rv_core_ibex_));
}

class AlertForceTest : public RvCoreIbexTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_alert_force(nullptr, kDifRvCoreIbexAlertFatalSwErr));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(dif_rv_core_ibex_alert_force(
      nullptr, static_cast<dif_rv_core_ibex_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(RV_CORE_IBEX_ALERT_TEST_REG_OFFSET,
                 {{RV_CORE_IBEX_ALERT_TEST_FATAL_SW_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_rv_core_ibex_alert_force(&rv_core_ibex_,
                                             kDifRvCoreIbexAlertFatalSwErr));

  // Force last alert.
  EXPECT_WRITE32(RV_CORE_IBEX_ALERT_TEST_REG_OFFSET,
                 {{RV_CORE_IBEX_ALERT_TEST_RECOV_HW_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_rv_core_ibex_alert_force(&rv_core_ibex_,
                                             kDifRvCoreIbexAlertRecovHwErr));
}

}  // namespace
}  // namespace dif_rv_core_ibex_autogen_unittest
