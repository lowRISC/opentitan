// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crc32.h"

#include <stdint.h>

#include "gtest/gtest.h"

namespace crc32_unittest {
namespace {

struct TestParams {
  std::string input;
  uint32_t exp_crc;
};

class CrcTest : public testing::TestWithParam<TestParams> {};

// Expected CRC32 values were generated using the following Python snippet:
// ```
// import zlib
// hex(zlib.crc32(b'<string>'))
// ```
INSTANTIATE_TEST_SUITE_P(AllCases, CrcTest,
                         testing::Values(
                             TestParams{
                                 "123456789",
                                 0xcbf43926,
                             },
                             TestParams{
                                 "The quick brown fox jumps over the lazy dog",
                                 0x414fa339,
                             }));

TEST_P(CrcTest, Crc32) {
  EXPECT_EQ(crc32(GetParam().input.data(), GetParam().input.length()),
            GetParam().exp_crc);
}

TEST_P(CrcTest, Crc32WithContext) {
  uint32_t ctx;
  crc32_init(&ctx);
  for (auto val : GetParam().input) {
    crc32_add(&ctx, val);
  }
  EXPECT_EQ(crc32_finish(&ctx), GetParam().exp_crc);
}

}  // namespace
}  // namespace crc32_unittest
