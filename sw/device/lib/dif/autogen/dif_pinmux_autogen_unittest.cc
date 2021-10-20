// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_pinmux_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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
  EXPECT_EQ(dif_pinmux_init({.base_addr = dev().region()}, nullptr),
            kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_pinmux_init({.base_addr = dev().region()}, &pinmux_), kDifOk);
}

}  // namespace
}  // namespace dif_pinmux_autogen_unittest
