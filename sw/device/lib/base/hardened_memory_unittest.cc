// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"

#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

// NOTE: This test does not verify hardening measures; it only checks that the
// "normal" contract of the functions is upheld.

namespace hardened_memory_unittest {
namespace {

using ::testing::Each;
using ::testing::ElementsAre;

TEST(HardenedMemory, Memcpy) {
  std::vector<uint32_t> xs = {1, 2, 3, 4, 5, 6, 7, 8};
  std::vector<uint32_t> ys(8);

  hardened_memcpy(ys.data(), xs.data(), 0);
  EXPECT_THAT(ys, Each(0));

  hardened_memcpy(ys.data() + 1, xs.data(), 7);
  EXPECT_THAT(ys, ElementsAre(0, 1, 2, 3, 4, 5, 6, 7));
}

constexpr uint32_t kRandomWord = 0xdeadbeef;

// Override whatever the default randomness source is so we can verify it
// actually gets used.
extern "C" size_t hardened_memshred_random_word() { return kRandomWord; }

TEST(HardenedMemory, MemShred) {
  std::vector<uint32_t> xs = {1, 2, 3, 4, 5, 6, 7, 8};
  hardened_memshred(xs.data(), xs.size());

  EXPECT_THAT(xs, Each(kRandomWord));
}

TEST(HardenedMemory, MemEq) {
  std::vector<uint32_t> xs = {1, 2, 3, 4, 5, 6, 7, 8};
  std::vector<uint32_t> ys = xs;

  EXPECT_EQ(hardened_memeq(ys.data(), xs.data(), xs.size()), kHardenedBoolTrue);

  ++ys[5];
  EXPECT_EQ(hardened_memeq(ys.data(), xs.data(), xs.size()),
            kHardenedBoolFalse);
}

}  // namespace
}  // namespace hardened_memory_unittest
