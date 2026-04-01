// Copyright lowRISC contributors (OpenTitan project).
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
extern "C" uint32_t hardened_memshred_random_word() { return kRandomWord; }

// Provides "randomness" for random_order.
extern "C" uint32_t random_order_random_word() { return kRandomWord; }

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

TEST(HardenedMemory, XorReversibility) {
  std::vector<uint32_t> xs = {0x11111111, 0x22222222, 0x33333333, 0x44444444};
  std::vector<uint32_t> ys = {0x55555555, 0x66666666, 0x77777777, 0x88888888};

  std::vector<uint32_t> masked(4);
  std::vector<uint32_t> unmasked(4);

  // Mask: xs ^ ys = masked
  hardened_xor(xs.data(), ys.data(), xs.size(), masked.data());

  // Unmask: masked ^ ys = unmasked
  hardened_xor(masked.data(), ys.data(), ys.size(), unmasked.data());

  EXPECT_EQ(unmasked, xs);
}

TEST(HardenedMemory, AddSubReversibility) {
  // We choose boundary values (0xFFFFFFFF and 0x00000000) to ensure the
  // carry/borrow chain logic triggers multiple times across word boundaries.
  std::vector<uint32_t> xs = {0x00000000, 0xFFFFFFFF, 0x00000000, 0xFFFFFFFF};
  std::vector<uint32_t> ys = {0x00000001, 0x00000002, 0xFFFFFFFF, 0x00000004};

  std::vector<uint32_t> sub_result(4);
  std::vector<uint32_t> add_result(4);

  // 1. Test Subtraction followed by Addition: (X - Y) + Y == X
  hardened_sub(xs.data(), ys.data(), xs.size(), sub_result.data());
  hardened_add(sub_result.data(), ys.data(), ys.size(), add_result.data());

  EXPECT_EQ(add_result, xs);

  std::vector<uint32_t> add_first(4);
  std::vector<uint32_t> sub_second(4);

  // 2. Test Addition followed by Subtraction: (X + Y) - Y == X
  hardened_add(xs.data(), ys.data(), xs.size(), add_first.data());
  hardened_sub(add_first.data(), ys.data(), ys.size(), sub_second.data());

  EXPECT_EQ(sub_second, xs);
}

}  // namespace
}  // namespace hardened_memory_unittest
