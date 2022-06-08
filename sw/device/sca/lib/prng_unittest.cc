// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/lib/prng.h"

#include <algorithm>
#include <array>
#include <iostream>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace sca_prng_unittest {
namespace {

constexpr std::array<uint8_t, 100> kExpected = {
    72,  23,  38,  22,  38,  209, 127, 139, 53,  97,  19,  224, 221, 255, 91,
    115, 23,  84,  227, 109, 125, 18,  75,  16,  114, 219, 106, 107, 144, 116,
    7,   83,  5,   135, 105, 243, 244, 73,  124, 204, 227, 123, 163, 63,  17,
    59,  0,   248, 126, 154, 56,  0,   136, 128, 174, 20,  111, 137, 127, 226,
    194, 17,  37,  20,  89,  228, 253, 35,  48,  190, 190, 16,  110, 239, 76,
    39,  89,  165, 151, 226, 94,  204, 12,  0,   182, 229, 151, 66,  79,  8,
    116, 133, 55,  2,   13,  160, 28,  55,  178, 60,
};

TEST(RandByte, Seed_0) {
  std::vector<uint8_t> actual(kExpected.size());

  prng_seed(0);
  std::generate(actual.begin(), actual.end(), prng_rand_byte);
  EXPECT_THAT(actual, testing::ElementsAreArray(kExpected));
}

TEST(RandBytes, Seed_0) {
  std::vector<uint8_t> actual(kExpected.size());

  prng_seed(0);
  prng_rand_bytes(actual.data(), actual.size());
  EXPECT_THAT(actual, testing::ElementsAreArray(kExpected));
}

}  // namespace
}  // namespace sca_prng_unittest
