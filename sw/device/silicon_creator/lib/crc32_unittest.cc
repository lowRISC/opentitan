// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crc32.h"

#include <cstring>
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
                             },
                             TestParams{
                                 "\xfe\xca\xfe\xca\x02\xb0\xad\x1b",
                                 0x9508ac14,
                             }));

TEST_P(CrcTest, Crc32) {
  EXPECT_EQ(crc32(GetParam().input.data(), GetParam().input.length()),
            GetParam().exp_crc);
}

TEST_P(CrcTest, Crc32Add) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add(&ctx, GetParam().input.data(), GetParam().input.length());

  EXPECT_EQ(crc32_finish(&ctx), GetParam().exp_crc);
}

TEST_F(CrcTest, Misaligned) {
  constexpr uint32_t kExpCrc = 0x414fa339;
  alignas(uint32_t) char input[] =
      ">The quick brown fox jumps over the lazy dog";

  EXPECT_EQ(crc32(&input[1], std::strlen(input) - 1), kExpCrc);

  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add(&ctx, &input[1], std::strlen(input) - 1);

  EXPECT_EQ(crc32_finish(&ctx), kExpCrc);
}

TEST_P(CrcTest, Crc32Add8) {
  uint32_t ctx;
  crc32_init(&ctx);
  for (auto val : GetParam().input) {
    crc32_add8(&ctx, val);
  }
  EXPECT_EQ(crc32_finish(&ctx), GetParam().exp_crc);
}

TEST_F(CrcTest, Crc32Add32) {
  uint32_t ctx;
  crc32_init(&ctx);
  constexpr uint32_t kExpCrc = 0x9508ac14;

  crc32_add32(&ctx, 0xcafecafe);
  crc32_finish(&ctx);
  crc32_add32(&ctx, 0x1badb002);

  EXPECT_EQ(crc32_finish(&ctx), kExpCrc);
}

}  // namespace
}  // namespace crc32_unittest
