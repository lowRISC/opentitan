// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/otbn_util.h"

#include "gtest/gtest.h"

namespace otbn_util_unittest {
namespace {

TEST(OtbnTest, OtbnInit) {
  otbn_t otbn;
  otbn_init(&otbn);
  EXPECT_EQ(otbn.app_is_loaded, kHardenedBoolFalse);
  EXPECT_EQ(otbn.error_bits, kOtbnErrBitsNoError);
}

}  // namespace
}  // namespace otbn_util_unittest
