// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/epmp.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace epmp_unittest {
namespace {

struct NapotCase {
  /**
   * Start / end of the NAPOT region.
   */
  uint32_t start;
  uint32_t end;
  /**
   * Encoded NAPOT address.
   */
  uint32_t encoded;
};

class NapotTest : public rom_test::RomTest,
                  public testing::WithParamInterface<NapotCase> {};

TEST_P(NapotTest, Codec) {
  epmp_region_t region = {
      .start = (uintptr_t)GetParam().start,
      .end = (uintptr_t)GetParam().end,
  };
  EXPECT_EQ(epmp_encode_napot(region), GetParam().encoded);

  epmp_region_t decoded = epmp_decode_napot(GetParam().encoded);
  EXPECT_EQ(decoded.start, GetParam().start);
  EXPECT_EQ(decoded.end, GetParam().end);
}

INSTANTIATE_TEST_SUITE_P(AllCases, NapotTest,
                         testing::Values(
                             NapotCase{
                                 .start = 0b1000010100100100101010100000,
                                 .end = 0b1000010100100100101011000000,
                                 .encoded = 0b10000101001001001010101011,
                             },
                             NapotCase{
                                 .start = 0b101000001101000011100000000000,
                                 .end = 0b101000001101000011100100000000,
                                 .encoded = 0b1010000011010000111000011111,
                             },
                             NapotCase{
                                 .start = 0b10111111111111111111111111111000,
                                 .end = 0b11000000000000000000000000000000,
                                 .encoded = 0b101111111111111111111111111110,
                             },
                             NapotCase{
                                 .start = 0b00000000000000000000000000000000,
                                 .end = 0b10000000000000000000000000000000,
                                 .encoded = 0b001111111111111111111111111111,
                             }));

}  // namespace
}  // namespace epmp_unittest
