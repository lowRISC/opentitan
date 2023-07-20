// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_pinmux_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "pinmux_regs.h"  // Generated.

namespace dif_pinmux_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class PinmuxTest : public Test, public MmioTest {
 protected:
  dif_pinmux_t pinmux_ = {.base_addr = dev().region()};
};

class InitTest : public PinmuxTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pinmux_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_pinmux_init(dev().region(), &pinmux_));
}

class AlertForceTest : public PinmuxTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pinmux_alert_force(nullptr, kDifPinmuxAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_pinmux_alert_force(nullptr, static_cast<dif_pinmux_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(PINMUX_ALERT_TEST_REG_OFFSET,
                 {{PINMUX_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_pinmux_alert_force(&pinmux_, kDifPinmuxAlertFatalFault));
}

}  // namespace
}  // namespace dif_pinmux_autogen_unittest
