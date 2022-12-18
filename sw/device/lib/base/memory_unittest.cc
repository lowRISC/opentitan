// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"

#include <algorithm>
#include <stdint.h>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest-message.h"
#include "gtest/gtest.h"

namespace memory_unittest {
namespace {

// Wrappers for builtins because they must be called directly when building with
// clang.

void *builtin_memcpy_wrapper(void *dest, const void *src, size_t count) {
  return __builtin_memcpy(dest, src, count);
}

int builtin_memcmp_wrapper(const void *lhs, const void *rhs, size_t count) {
  return __builtin_memcmp(lhs, rhs, count);
}

void *builtin_memset_wrapper(void *dest, int ch, size_t count) {
  return __builtin_memset(dest, ch, count);
}

// Reference implementations of memory functions.

enum {
  kMemCmpEq = 0,
  kMemCmpLt = -42,
  kMemCmpGt = 42,
};

int ref_memrcmp(const void *lhs, const void *rhs, size_t len) {
  const uint8_t *lhs8 = (uint8_t *)lhs;
  const uint8_t *rhs8 = (uint8_t *)rhs;
  size_t j;
  for (size_t i = 0; i < len; ++i) {
    j = len - 1 - i;
    if (lhs8[j] < rhs8[j]) {
      return kMemCmpLt;
    } else if (lhs8[j] > rhs8[j]) {
      return kMemCmpGt;
    }
  }
  return kMemCmpEq;
}

void *ref_memchr(const void *ptr, int value, size_t len) {
  uint8_t *ptr8 = (uint8_t *)ptr;
  uint8_t value8 = (uint8_t)value;
  for (size_t i = 0; i < len; ++i) {
    if (ptr8[i] == value8) {
      return ptr8 + i;
    }
  }
  return nullptr;
}

void *ref_memrchr(const void *ptr, int value, size_t len) {
  uint8_t *ptr8 = (uint8_t *)ptr;
  uint8_t value8 = (uint8_t)value;
  for (size_t i = 0; i < len; ++i) {
    size_t idx = len - i - 1;
    if (ptr8[idx] == value8) {
      return ptr8 + idx;
    }
  }
  return nullptr;
}

// Parameterized test suites enable us to run the same tests against each memory
// function and its builtin equivalent (or reference implementation when there
// is no builtin). We can also run the same tests on any "r" variants that
// operate from right to left.
class MemCpyTest : public ::testing::TestWithParam<decltype(&ot_memcpy)> {};
class MemCmpTest : public ::testing::TestWithParam<decltype(&ot_memcmp)> {};
class MemSetTest : public ::testing::TestWithParam<decltype(&ot_memset)> {};
class MemChrTest : public ::testing::TestWithParam<decltype(&ot_memchr)> {};

INSTANTIATE_TEST_SUITE_P(MemCpy, MemCpyTest,
                         ::testing::Values(ot_memcpy, builtin_memcpy_wrapper));
INSTANTIATE_TEST_SUITE_P(MemCmp, MemCmpTest,
                         ::testing::Values(ot_memcmp, builtin_memcmp_wrapper,
                                           memrcmp, ref_memrcmp));
INSTANTIATE_TEST_SUITE_P(MemSet, MemSetTest,
                         ::testing::Values(ot_memset, builtin_memset_wrapper));
INSTANTIATE_TEST_SUITE_P(MemChr, MemChrTest,
                         ::testing::Values(ot_memchr, ref_memchr, ot_memrchr,
                                           ref_memrchr));

using ::testing::Each;
using ::testing::ElementsAre;

TEST_P(MemCpyTest, Simple) {
  auto memcpy_func = GetParam();

  static constexpr size_t kLen = 8;
  std::vector<uint32_t> xs = {1, 2, 3, 4, 5, 6, 7, 8};
  std::vector<uint32_t> ys(kLen);
  ASSERT_EQ(xs.size(), kLen);

  // Copy `xs[:-1]` to `ys[1:]`.
  memcpy_func(ys.data() + 1, xs.data(), (kLen - 1) * sizeof(uint32_t));
  EXPECT_THAT(ys, ElementsAre(0, 1, 2, 3, 4, 5, 6, 7));

  // Copy `xs[:-1]` to `ys[:-1]`.
  memcpy_func(ys.data(), xs.data(), (kLen - 1) * sizeof(uint32_t));
  EXPECT_THAT(ys, ElementsAre(1, 2, 3, 4, 5, 6, 7, 7));

  // Copy `xs[:-2]` to `ys[2:]`.
  memcpy_func(&ys[2], xs.data(), (kLen - 2) * sizeof(uint32_t));
  EXPECT_THAT(ys, ElementsAre(1, 2, 1, 2, 3, 4, 5, 6));
}

TEST_P(MemCpyTest, VaryingSize) {
  auto memcpy_func = GetParam();

  static constexpr size_t kLen = 8;
  static constexpr uint32_t kZeroes[kLen] = {0};
  std::vector<uint32_t> xs = {1, 2, 3, 4, 5, 6, 7, 8};
  ASSERT_EQ(xs.size(), kLen);

  for (size_t i = 0; i < kLen; ++i) {
    // Zero out `xs[:i]`.
    memcpy_func(xs.data(), kZeroes, i * sizeof(uint32_t));

    std::vector<uint32_t> expected = {1, 2, 3, 4, 5, 6, 7, 8};
    std::fill_n(/*first=*/expected.begin(), /*count=*/i, /*value=*/0);
    EXPECT_EQ(xs, expected) << "i=" << i;
  }
}

TEST_P(MemCpyTest, VarySrcAlignment) {
  auto memcpy_func = GetParam();

  static constexpr size_t kLen = 8;
  const std::vector<uint32_t> xs_original = {1, 2, 3, 4, 5, 6, 7, 8};
  ASSERT_EQ(xs_original.size(), kLen);

  const std::vector<uint32_t> ys = {11, 12, 13, 14, 15, 16, 17, 18};
  ASSERT_EQ(ys.size(), kLen);

  for (size_t i = 0; i < kLen; ++i) {
    SCOPED_TRACE(testing::Message() << "i=" << i);

    std::vector<uint32_t> xs(xs_original);

    // Copy `ys[i:]` to `xs[:-i]`.
    const size_t num_u32_to_copy = kLen - i;
    memcpy_func(xs.data(), &ys[i], num_u32_to_copy * sizeof(uint32_t));

    std::vector<uint32_t> xs_expected(xs_original);
    for (size_t j = 0; j < num_u32_to_copy; ++j) {
      xs_expected[j] = 11 + i + j;
    }
    EXPECT_EQ(xs, xs_expected);
  }
}

TEST_P(MemCpyTest, VaryDestAlignment) {
  auto memcpy_func = GetParam();

  static constexpr size_t kLen = 8;
  const std::vector<uint32_t> xs_original = {1, 2, 3, 4, 5, 6, 7, 8};
  ASSERT_EQ(xs_original.size(), kLen);

  const std::vector<uint32_t> ys = {11, 12, 13, 14, 15, 16, 17, 18};
  ASSERT_EQ(ys.size(), kLen);

  for (size_t i = 0; i < kLen; ++i) {
    SCOPED_TRACE(testing::Message() << "i=" << i);

    std::vector<uint32_t> xs(xs_original);

    // Copy `ys[:-i]` to `xs[i:]`.
    const size_t num_u32_to_copy = kLen - i;
    memcpy_func(&xs[i], ys.data(), num_u32_to_copy * sizeof(uint32_t));

    std::vector<uint32_t> xs_expected(xs_original);
    for (size_t j = 0; j < num_u32_to_copy; ++j) {
      xs_expected[j + i] = 11 + j;
    }

    EXPECT_EQ(xs, xs_expected);
  }
}

TEST_P(MemCmpTest, NullParam) {
  auto memcmp_func = GetParam();

  const uint8_t data[16] = {0};
  EXPECT_EQ(memcmp_func(nullptr, nullptr, 0), 0);
  EXPECT_EQ(memcmp_func(data, nullptr, 0), 0);
  EXPECT_EQ(memcmp_func(nullptr, data, 0), 0);
  EXPECT_EQ(memcmp_func(data, data, 0), 0);
}

TEST_P(MemCmpTest, ZeroesVaryingOffsetsAndLengths) {
  auto memcmp_func = GetParam();

  const uint8_t data[16] = {0};
  for (size_t offset = 0; offset <= 8; offset++) {
    for (size_t len = 0; len < 8; len++) {
      EXPECT_EQ(memcmp_func(data, data, len), 0);
      EXPECT_EQ(memcmp_func(data, data + offset, len), 0);
      EXPECT_EQ(memcmp_func(data + offset, data, len), 0);
      EXPECT_EQ(memcmp_func(data + offset, data + offset, len), 0);
    }
  }
}

TEST_P(MemSetTest, Null) {
  auto memset_func = GetParam();

  EXPECT_EQ(memset_func(nullptr, 0, 0), nullptr);
}

TEST_P(MemCmpTest, Properties) {
  auto memcmp_func = GetParam();

  constexpr size_t kLen = 5;
  constexpr uint8_t xs[kLen] = {0, 0, 0, 0, 0};
  constexpr uint8_t ys[kLen] = {0, 0, 0, 1, 3};
  constexpr uint8_t zs[kLen] = {0, 0, 0, 1, 4};

  // Reflexive property.
  EXPECT_EQ(memcmp_func(xs, xs, kLen), 0);
  EXPECT_EQ(memcmp_func(ys, ys, kLen), 0);
  EXPECT_EQ(memcmp_func(zs, zs, kLen), 0);
  // Transitive property for less-than result.
  EXPECT_LT(memcmp_func(xs, ys, kLen), 0);
  EXPECT_LT(memcmp_func(ys, zs, kLen), 0);
  EXPECT_LT(memcmp_func(xs, zs, kLen), 0);
  // Transitive property for greater-than result.
  EXPECT_GT(memcmp_func(ys, xs, kLen), 0);
  EXPECT_GT(memcmp_func(zs, ys, kLen), 0);
  EXPECT_GT(memcmp_func(zs, xs, kLen), 0);
}

TEST_P(MemCmpTest, DoesNotUseSystemEndianness) {
  auto memcmp_func = GetParam();

  const bool reverse = memcmp_func == &memrcmp || memcmp_func == &ref_memrcmp;

  constexpr uint8_t kBuf1[] = {0, 0, 0, 1};
  constexpr uint8_t kBuf2[] = {0, 0, 1, 0};

  if (!reverse) {
    // A lexicographic, byte-wise comparison will see that `kBuf1 < kBuf2`, but
    // a naive word-wise comparison might think that `kBuf1 > kBuf2` because it
    // interprets `kBuf1` as 0x01000000 and `kBuf2` as 0x00010000 and compares
    // `uint32_t` values.
    EXPECT_LT(memcmp_func(kBuf1, kBuf2, sizeof(kBuf1)), 0);
  } else {
    EXPECT_GT(memcmp_func(kBuf1, kBuf2, sizeof(kBuf1)), 0);
  }
}

TEST_P(MemSetTest, Simple) {
  auto memset_func = GetParam();

  for (uint32_t len = 0; len < 32; ++len) {
    SCOPED_TRACE(testing::Message() << "len = " << len);

    std::vector<uint32_t> xs(len, 123);
    EXPECT_THAT(xs, Each(123));
    EXPECT_EQ(memset_func(xs.data(), 0, xs.size() * sizeof(uint32_t)),
              xs.data());
    EXPECT_THAT(xs, Each(0));
  }
}

TEST_P(MemChrTest, Null) {
  auto memchr_func = GetParam();

  EXPECT_EQ(memchr_func(nullptr, 0, 0), nullptr);
  EXPECT_EQ(memchr_func(nullptr, 42, 0), nullptr);
}

TEST_P(MemChrTest, NonNullButEmpty) {
  auto memchr_func = GetParam();

  const uint8_t kEmpty[] = {};
  static_assert(sizeof(kEmpty) == 0, "kEmpty should contain zero bytes");

  EXPECT_EQ(memchr_func(kEmpty, 0, sizeof(kEmpty)), nullptr);
  EXPECT_EQ(memchr_func(kEmpty, 42, sizeof(kEmpty)), nullptr);
}

TEST_P(MemChrTest, Simple) {
  auto memchr_func = GetParam();

  std::vector<uint8_t> vec = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  EXPECT_EQ(memchr_func(vec.data(), 0, vec.size()), vec.data());
  EXPECT_EQ(memchr_func(vec.data(), 5, vec.size()), vec.data() + 5);

  constexpr size_t kLen = 11;
  constexpr uint8_t data[kLen] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  EXPECT_EQ(memchr_func(data, 0, kLen), data);
  EXPECT_EQ(memchr_func(data, 1, kLen), data + 1);
  EXPECT_EQ(memchr_func(data, 4, kLen), data + 4);
  EXPECT_EQ(memchr_func(data, 8, kLen), data + 8);
  EXPECT_EQ(memchr_func(data, 42, kLen), nullptr);
}

TEST_P(MemChrTest, VaryingLengths) {
  auto memchr_func = GetParam();

  for (size_t len = 0; len < 16; ++len) {
    std::vector<uint8_t> vec;
    vec.reserve(len);
    for (size_t i = 0; i < len; ++i) {
      vec.push_back(static_cast<uint8_t>(i));
    }
    // Search for each value.
    for (size_t i = 0; i < len; ++i) {
      EXPECT_EQ(memchr_func(vec.data(), i, len), vec.data() + i);
    }
    // Search for a value that is not in the vector.
    EXPECT_EQ(memchr_func(vec.data(), len + 1, len), nullptr);
  }
}

TEST_P(MemChrTest, RepeatedBytes) {
  auto memchr_func = GetParam();

  const bool reverse =
      memchr_func == &ot_memrchr || memchr_func == &ref_memrchr;

  // Define a buffer that contains repeated bytes at a variety of offsets.
  constexpr uint8_t kBuf[] = {// No repeated bytes yet.
                              0, 1, 2, 3,
                              // First byte is repeated once.
                              4, 4, 5, 6,
                              // Second byte is repeated once
                              7, 8, 8, 9,
                              // Third byte is repeated once.
                              10, 11, 12, 12,
                              // First byte is repeated three times.
                              13, 13, 13, 14,
                              // Second byte is repeated three times.
                              15, 16, 16, 16,
                              // First byte is repeated four times.
                              17, 17, 17, 17};

  EXPECT_EQ(memchr_func(kBuf, 0, sizeof(kBuf)), kBuf);
  EXPECT_EQ(memchr_func(kBuf, 1, sizeof(kBuf)), kBuf + 1);
  EXPECT_EQ(memchr_func(kBuf, 2, sizeof(kBuf)), kBuf + 2);
  EXPECT_EQ(memchr_func(kBuf, 3, sizeof(kBuf)), kBuf + 3);
  EXPECT_EQ(memchr_func(kBuf, 4, sizeof(kBuf)), reverse ? kBuf + 5 : kBuf + 4);
  EXPECT_EQ(memchr_func(kBuf, 5, sizeof(kBuf)), kBuf + 6);
  EXPECT_EQ(memchr_func(kBuf, 6, sizeof(kBuf)), kBuf + 7);
  EXPECT_EQ(memchr_func(kBuf, 7, sizeof(kBuf)), kBuf + 8);
  EXPECT_EQ(memchr_func(kBuf, 8, sizeof(kBuf)), reverse ? kBuf + 10 : kBuf + 9);
  EXPECT_EQ(memchr_func(kBuf, 9, sizeof(kBuf)), kBuf + 11);
  EXPECT_EQ(memchr_func(kBuf, 10, sizeof(kBuf)), kBuf + 12);
  EXPECT_EQ(memchr_func(kBuf, 11, sizeof(kBuf)), kBuf + 13);
  EXPECT_EQ(memchr_func(kBuf, 12, sizeof(kBuf)),
            reverse ? kBuf + 15 : kBuf + 14);
  EXPECT_EQ(memchr_func(kBuf, 13, sizeof(kBuf)),
            reverse ? kBuf + 18 : kBuf + 16);
  EXPECT_EQ(memchr_func(kBuf, 14, sizeof(kBuf)), kBuf + 19);
  EXPECT_EQ(memchr_func(kBuf, 15, sizeof(kBuf)), kBuf + 20);
  EXPECT_EQ(memchr_func(kBuf, 16, sizeof(kBuf)),
            reverse ? kBuf + 23 : kBuf + 21);
  EXPECT_EQ(memchr_func(kBuf, 17, sizeof(kBuf)),
            reverse ? kBuf + 27 : kBuf + 24);
}

}  // namespace
}  // namespace memory_unittest
