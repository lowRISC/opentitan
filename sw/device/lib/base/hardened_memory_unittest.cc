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

TEST(HardenedMemory, RangeCheck) {
  // Single-word tests
  std::vector<uint32_t> n_single = {10};

  std::vector<uint32_t> val_single_zero = {0};
  std::vector<uint32_t> val_single_valid = {5};
  std::vector<uint32_t> val_single_equal = {10};
  std::vector<uint32_t> val_single_large = {15};

  EXPECT_EQ(
      hardened_range_check(val_single_zero.data(), n_single.data(), 1).value,
      OTCRYPTO_BAD_ARGS.value);

  EXPECT_EQ(
      hardened_range_check(val_single_valid.data(), n_single.data(), 1).value,
      OTCRYPTO_OK.value);

  EXPECT_EQ(
      hardened_range_check(val_single_equal.data(), n_single.data(), 1).value,
      OTCRYPTO_BAD_ARGS.value);

  EXPECT_EQ(
      hardened_range_check(val_single_large.data(), n_single.data(), 1).value,
      OTCRYPTO_BAD_ARGS.value);

  // Multi-word tests
  std::vector<uint32_t> n_multi = {0x00000000, 0x00000002};
  std::vector<uint32_t> val_multi_zero = {0x00000000, 0x00000000};
  std::vector<uint32_t> val_multi_valid = {0xFFFFFFFF, 0x00000001};
  std::vector<uint32_t> val_multi_equal = {0x00000000, 0x00000002};
  std::vector<uint32_t> val_multi_large = {0x00000001, 0x00000002};

  EXPECT_EQ(
      hardened_range_check(val_multi_zero.data(), n_multi.data(), 2).value,
      OTCRYPTO_BAD_ARGS.value);

  EXPECT_EQ(
      hardened_range_check(val_multi_valid.data(), n_multi.data(), 2).value,
      OTCRYPTO_OK.value);

  EXPECT_EQ(
      hardened_range_check(val_multi_equal.data(), n_multi.data(), 2).value,
      OTCRYPTO_BAD_ARGS.value);

  EXPECT_EQ(
      hardened_range_check(val_multi_large.data(), n_multi.data(), 2).value,
      OTCRYPTO_BAD_ARGS.value);
}

TEST(HardenedMemory, ModReduce) {
  // P-256 curve order.
  const size_t kP256ScalarWords = 8;
  std::vector<uint32_t> n = {0xfc632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad,
                             0xffffffff, 0xffffffff, 0x00000000, 0xffffffff};

  // Test case 1: value < n
  std::vector<uint32_t> val1 = {0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc, 0xdddddddd,
                                0xeeeeeeee, 0xffffffff, 0x00000000, 0x11111111};
  std::vector<uint32_t> res1(kP256ScalarWords);
  hardened_mod_reduce(val1.data(), n.data(), kP256ScalarWords, res1.data());
  EXPECT_EQ(res1, val1);

  // Test case 2: value == n
  std::vector<uint32_t> val2 = n;
  std::vector<uint32_t> res2(kP256ScalarWords);
  std::vector<uint32_t> exp2(kP256ScalarWords, 0);
  hardened_mod_reduce(val2.data(), n.data(), kP256ScalarWords, res2.data());
  EXPECT_EQ(res2, exp2);

  // Test case 3: value > n
  std::vector<uint32_t> val3 = {0xfe632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad,
                                0xffffffff, 0xffffffff, 0x00000000, 0xffffffff};
  std::vector<uint32_t> res3(kP256ScalarWords);
  std::vector<uint32_t> exp3 = {0x02000000, 0x00000000, 0x00000000, 0x00000000,
                                0x00000000, 0x00000000, 0x00000000, 0x00000000};
  hardened_mod_reduce(val3.data(), n.data(), kP256ScalarWords, res3.data());
  EXPECT_EQ(res3, exp3);

  // Test case 4: value is 2*n handled with overflow.
  std::vector<uint32_t> val4(kP256ScalarWords);
  hardened_add(n.data(), n.data(), kP256ScalarWords, val4.data());
  std::vector<uint32_t> res4(kP256ScalarWords);
  // Since hardened_add overflows, val4 = 2*n - 2^256, which is < n.
  // So the result of modular reduction should be val4 itself.
  std::vector<uint32_t> exp4 = val4;
  hardened_mod_reduce(val4.data(), n.data(), kP256ScalarWords, res4.data());
  EXPECT_EQ(res4, exp4);

  // Test case 5: n + 1 mod n = 1.
  std::vector<uint32_t> one(kP256ScalarWords, 0);
  one[0] = 1;
  std::vector<uint32_t> val5(kP256ScalarWords);
  hardened_add(n.data(), one.data(), kP256ScalarWords, val5.data());
  std::vector<uint32_t> res5(kP256ScalarWords);
  hardened_mod_reduce(val5.data(), n.data(), kP256ScalarWords, res5.data());
  EXPECT_EQ(res5, one);
}

TEST(HardenedMemory, SubMod) {
  // P-256 curve order.
  const size_t kP256ScalarWords = 8;
  std::vector<uint32_t> n = {0xfc632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad,
                             0xffffffff, 0xffffffff, 0x00000000, 0xffffffff};
  std::vector<uint32_t> res(kP256ScalarWords);

  // Test case 1: x > y => 5 - 2 = 3
  std::vector<uint32_t> x1(kP256ScalarWords, 0);
  x1[0] = 5;
  std::vector<uint32_t> y1(kP256ScalarWords, 0);
  y1[0] = 2;
  std::vector<uint32_t> exp1(kP256ScalarWords, 0);
  exp1[0] = 3;
  hardened_sub_mod(x1.data(), y1.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp1);

  // Test case 2: x < y => 2 - 5 mod n = n - 3
  std::vector<uint32_t> x2(kP256ScalarWords, 0);
  x2[0] = 2;
  std::vector<uint32_t> y2(kP256ScalarWords, 0);
  y2[0] = 5;
  std::vector<uint32_t> exp2 = n;
  exp2[0] -= 3;
  hardened_sub_mod(x2.data(), y2.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp2);

  // Test case 3: x == y => 0
  std::vector<uint32_t> x3 = {0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc, 0xdddddddd,
                              0xeeeeeeee, 0xffffffff, 0x00000000, 0x11111111};
  std::vector<uint32_t> exp3(kP256ScalarWords, 0);
  hardened_sub_mod(x3.data(), x3.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp3);

  // Test case 4: multi-word x > y
  std::vector<uint32_t> x4 = {0xfe632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad,
                              0xffffffff, 0xffffffff, 0x00000000, 0xffffffff};
  std::vector<uint32_t> y4 = {0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc, 0xdddddddd,
                              0xeeeeeeee, 0xffffffff, 0x00000000, 0x11111111};
  std::vector<uint32_t> exp4(kP256ScalarWords);
  hardened_sub(x4.data(), y4.data(), kP256ScalarWords, exp4.data());
  hardened_sub_mod(x4.data(), y4.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp4);
}

TEST(HardenedMemory, AddMod) {
  // P-256 curve order.
  const size_t kP256ScalarWords = 8;
  std::vector<uint32_t> n = {0xfc632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad,
                             0xffffffff, 0xffffffff, 0x00000000, 0xffffffff};
  std::vector<uint32_t> res(kP256ScalarWords);

  // Test case 1: x + y < n => 5 + 2 = 7
  std::vector<uint32_t> x1(kP256ScalarWords, 0);
  x1[0] = 5;
  std::vector<uint32_t> y1(kP256ScalarWords, 0);
  y1[0] = 2;
  std::vector<uint32_t> exp1(kP256ScalarWords, 0);
  exp1[0] = 7;
  hardened_add_mod(x1.data(), y1.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp1);

  // Test case 2: x + y > n => (n - 1) + 2 mod n = 1
  std::vector<uint32_t> x2 = {0xfc632550, 0xf3b9cac2, 0xa7179e84, 0xbce6faad,
                              0xffffffff, 0xffffffff, 0x00000000, 0xffffffff};
  std::vector<uint32_t> y2(kP256ScalarWords, 0);
  y2[0] = 2;
  std::vector<uint32_t> exp2(kP256ScalarWords, 0);
  exp2[0] = 1;
  hardened_add_mod(x2.data(), y2.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp2);

  // Test case 3: x + y overflows
  std::vector<uint32_t> x3 = {0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
                              0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff};

  std::vector<uint32_t> exp3(kP256ScalarWords);
  std::vector<uint32_t> sum3(kP256ScalarWords);
  hardened_add(x3.data(), x3.data(), kP256ScalarWords, sum3.data());
  hardened_mod_reduce(sum3.data(), n.data(), kP256ScalarWords, exp3.data());

  hardened_add_mod(x3.data(), x3.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp3);

  // Test case 4: multi-word x + y < n
  std::vector<uint32_t> x4 = {0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1};
  std::vector<uint32_t> y4 = {0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1};
  std::vector<uint32_t> exp4 = {0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2};
  hardened_add_mod(x4.data(), y4.data(), n.data(), kP256ScalarWords,
                   res.data());
  EXPECT_EQ(res, exp4);
}

}  // namespace
}  // namespace hardened_memory_unittest
