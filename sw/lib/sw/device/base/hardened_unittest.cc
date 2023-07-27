// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"

#include <limits>
#include <type_traits>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace hardened_unittest {
namespace {

MATCHER(IsZero, "is zero") { return arg == 0; }

MATCHER(IsAllOnes, "is all ones") {
  return arg ==
         std::numeric_limits<std::remove_reference_t<decltype(arg)>>::max();
}

TEST(ConstTime, Sltz) {
  EXPECT_THAT(ct_sltz32(42), IsZero());
  EXPECT_THAT(ct_sltz32(0), IsZero());
  EXPECT_THAT(ct_sltz32(-42), IsAllOnes());

  EXPECT_THAT(ct_sltzw(42), IsZero());
  EXPECT_THAT(ct_sltzw(0), IsZero());
  EXPECT_THAT(ct_sltzw(-42), IsAllOnes());
}

TEST(ConstTime, Slt) {
  EXPECT_THAT(ct_sltu32(42, 120), IsAllOnes());
  EXPECT_THAT(ct_sltu32(192874, 1231), IsZero());
  EXPECT_THAT(ct_sltu32(12121212, 12121212), IsZero());
  EXPECT_THAT(ct_sltu32(0, 0), IsZero());

  EXPECT_THAT(ct_sltuw(42, 120), IsAllOnes());
  EXPECT_THAT(ct_sltuw(192874, 1231), IsZero());
  EXPECT_THAT(ct_sltuw(12121212, 12121212), IsZero());
  EXPECT_THAT(ct_sltuw(0, 0), IsZero());
}

TEST(ConstTime, Seqz) {
  EXPECT_THAT(ct_seqz32(0), IsAllOnes());
  EXPECT_THAT(ct_seqz32(1), IsZero());
  EXPECT_THAT(ct_seqz32(42), IsZero());

  EXPECT_THAT(ct_seqzw(0), IsAllOnes());
  EXPECT_THAT(ct_seqzw(1), IsZero());
  EXPECT_THAT(ct_seqzw(42), IsZero());
}

TEST(ConstTime, Seq) {
  EXPECT_THAT(ct_seq32(42, 120), IsZero());
  EXPECT_THAT(ct_seq32(192874, 1231), IsZero());
  EXPECT_THAT(ct_seq32(12121212, 12121212), IsAllOnes());
  EXPECT_THAT(ct_seq32(0, 0), IsAllOnes());

  EXPECT_THAT(ct_seqw(42, 120), IsZero());
  EXPECT_THAT(ct_seqw(192874, 1231), IsZero());
  EXPECT_THAT(ct_seqw(12121212, 12121212), IsAllOnes());
  EXPECT_THAT(ct_seqw(0, 0), IsAllOnes());
}

TEST(ConstTime, Cmov) {
  EXPECT_EQ(ct_cmov32(-1, 0xdeadbeef, 0xc0ffee), 0xdeadbeef);
  EXPECT_EQ(ct_cmov32(0, 0xdeadbeef, 0xc0ffee), 0xc0ffee);

  EXPECT_EQ(ct_cmovw(-1, 0xdeadbeef, 0xc0ffee), 0xdeadbeef);
  EXPECT_EQ(ct_cmovw(0, 0xdeadbeef, 0xc0ffee), 0xc0ffee);
}

}  // namespace
}  // namespace hardened_unittest
