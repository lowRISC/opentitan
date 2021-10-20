// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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
  EXPECT_EQ(dif_lc_ctrl_init({.base_addr = dev().region()}, nullptr),
            kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_lc_ctrl_init({.base_addr = dev().region()}, &lc_ctrl_), kDifOk);
}

}  // namespace
}  // namespace dif_lc_ctrl_autogen_unittest
