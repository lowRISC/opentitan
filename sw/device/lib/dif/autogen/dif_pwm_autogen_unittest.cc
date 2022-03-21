// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_pwm_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "pwm_regs.h"  // Generated.

namespace dif_pwm_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class PwmTest : public Test, public MmioTest {
 protected:
  dif_pwm_t pwm_ = {.base_addr = dev().region()};
};

class InitTest : public PwmTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_pwm_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_pwm_init(dev().region(), &pwm_), kDifOk);
}

class AlertForceTest : public PwmTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_pwm_alert_force(nullptr, kDifPwmAlertFatalFault), kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(dif_pwm_alert_force(nullptr, static_cast<dif_pwm_alert_t>(32)),
            kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(PWM_ALERT_TEST_REG_OFFSET,
                 {{PWM_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_EQ(dif_pwm_alert_force(&pwm_, kDifPwmAlertFatalFault), kDifOk);
}

}  // namespace
}  // namespace dif_pwm_autogen_unittest
