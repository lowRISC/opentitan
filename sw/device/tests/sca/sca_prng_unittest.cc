// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <algorithm>
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/sca/lib/prng.h"

namespace sca_prng_unittest {
namespace {

/**
 * First 100 return values of `random.randint(0, 255)` with a seed value of `0`.
 */
constexpr std::array<uint8_t, 100> kExpected = {
    197, 215, 20,  132, 248, 207, 155, 244, 183, 111, 71,  144, 71,  48,  128,
    75,  158, 50,  37,  169, 241, 51,  181, 222, 161, 104, 244, 226, 133, 31,
    7,   47,  204, 0,   252, 170, 124, 166, 32,  97,  113, 122, 72,  229, 46,
    41,  163, 250, 55,  154, 149, 63,  170, 104, 147, 227, 46,  197, 162, 123,
    148, 94,  96,  95,  16,  133, 243, 35,  45,  66,  76,  19,  41,  200, 141,
    120, 110, 214, 140, 230, 252, 182, 42,  166, 59,  249, 171, 97,  124, 8,
    138, 59,  112, 190, 87,  170, 218, 31,  51,  74};

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
