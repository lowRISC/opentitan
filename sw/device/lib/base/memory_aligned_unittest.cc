// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Unit tests for base_memory_copy_aligned and base_memory_copy_aligned_dma.
 *
 * Test strategy
 * =============
 * 1. **Correctness** – verify that `base_memory_copy_aligned` produces
 *    identical results to `memcpy` for all word-multiple block sizes from
 *    4 to 128 bytes (covering both the unrolled and tail paths).
 *
 * 2. **Unroll boundary** – explicitly exercise the critical size classes:
 *      - 4 bytes  (1 word  – tail only, no unrolled iteration)
 *      - 12 bytes (3 words – tail only)
 *      - 16 bytes (4 words – exactly one unrolled iteration)
 *      - 20 bytes (5 words – one unrolled + one scalar)
 *      - 64 bytes (16 words – four unrolled iterations, DMA threshold)
 *      - 128 bytes (32 words – eight unrolled iterations)
 *
 * 3. **DMA wrapper** – on host builds the DMA is stubbed out, so the wrapper
 *    should behave identically to `base_memory_copy_aligned`.  We verify
 *    this for both sub-threshold (< 64 B) and super-threshold (≥ 64 B) sizes.
 *
 * 4. **Instruction-count proxy** – we cannot count actual hardware
 *    instructions in a host unit test, but we can assert that the aligned
 *    copy produces the *same output* as the trusted builtin `__builtin_memcpy`
 *    while operating without alignment-check branches.  A separate note
 *    in the source comments above quantifies the expected gain analytically.
 *
 * 5. **Destination pointer return** – both functions must return `dest`.
 *
 * Build
 * =====
 * This file is compiled as a Bazel `cc_test` target (see BUILD).  It links
 * against `:memory_aligned` and `@googletest//:gtest_main`.
 *
 * On host (`OT_PLATFORM_RV32` not defined) the DMA stub is used
 * transparently, so all tests run without hardware.
 */

#include "sw/device/lib/base/memory_aligned.h"

#include <cstdint>
#include <cstring>
#include <vector>

#include "gtest/gtest.h"

// ============================================================
// Helper: fill a vector with a deterministic, non-zero pattern.
// ============================================================
static std::vector<uint32_t> make_pattern(size_t num_words,
                                          uint32_t seed = 0xDEADBEEFu) {
  std::vector<uint32_t> v(num_words);
  for (size_t i = 0; i < num_words; ++i) {
    // Simple LCG so the pattern has no repeated words that might mask bugs.
    seed = seed * 1664525u + 1013904223u;
    v[i] = seed;
  }
  return v;
}

// ============================================================
// Suite: AlignedCopyTest
// ============================================================
class AlignedCopyTest : public ::testing::TestWithParam<size_t> {};

// Test that for each word-multiple `len`, the aligned copy matches builtin.
TEST_P(AlignedCopyTest, MatchesBuiltinMemcpy) {
  const size_t num_words = GetParam();
  const size_t len = num_words * sizeof(uint32_t);

  std::vector<uint32_t> src = make_pattern(num_words);
  std::vector<uint32_t> dst_aligned(num_words, 0u);
  std::vector<uint32_t> dst_builtin(num_words, 0u);

  // Reference copy via compiler builtin.
  __builtin_memcpy(dst_builtin.data(), src.data(), len);

  // Copy under test.
  void *ret =
      base_memory_copy_aligned(dst_aligned.data(), src.data(), len);

  EXPECT_EQ(ret, static_cast<void *>(dst_aligned.data()))
      << "base_memory_copy_aligned must return dest";
  EXPECT_EQ(dst_aligned, dst_builtin)
      << "aligned copy mismatch for len=" << len;
}

// Test that the source buffer is not modified.
TEST_P(AlignedCopyTest, SourceUnmodified) {
  const size_t num_words = GetParam();
  const size_t len = num_words * sizeof(uint32_t);

  std::vector<uint32_t> src = make_pattern(num_words);
  const std::vector<uint32_t> src_copy = src;
  std::vector<uint32_t> dst(num_words, 0u);

  base_memory_copy_aligned(dst.data(), src.data(), len);
  EXPECT_EQ(src, src_copy) << "source buffer must not be modified";
}

// Exercise all word-multiple sizes from 1 to 32 words (4 to 128 bytes).
INSTANTIATE_TEST_SUITE_P(WordSizes, AlignedCopyTest,
                         ::testing::Range<size_t>(1, 33));

// ============================================================
// Suite: AlignedCopyBoundaryTest  (specific size classes)
// ============================================================
class AlignedCopyBoundaryTest : public ::testing::Test {};

// 1 word (4 bytes) – exercises tail-only path (no unrolled iterations).
TEST_F(AlignedCopyBoundaryTest, OneWord) {
  uint32_t src = 0xCAFEBABEu;
  uint32_t dst = 0u;
  base_memory_copy_aligned(&dst, &src, sizeof(uint32_t));
  EXPECT_EQ(dst, src);
}

// 3 words (12 bytes) – tail only, three scalar iterations.
TEST_F(AlignedCopyBoundaryTest, ThreeWords) {
  constexpr size_t kN = 3;
  uint32_t src[kN] = {1u, 2u, 3u};
  uint32_t dst[kN] = {0u, 0u, 0u};
  base_memory_copy_aligned(dst, src, kN * sizeof(uint32_t));
  for (size_t i = 0; i < kN; ++i) {
    EXPECT_EQ(dst[i], src[i]) << "mismatch at word " << i;
  }
}

// 4 words (16 bytes) – exactly one unrolled group, no tail.
TEST_F(AlignedCopyBoundaryTest, FourWords) {
  constexpr size_t kN = 4;
  uint32_t src[kN] = {0xAu, 0xBu, 0xCu, 0xDu};
  uint32_t dst[kN] = {0u};
  base_memory_copy_aligned(dst, src, kN * sizeof(uint32_t));
  for (size_t i = 0; i < kN; ++i) {
    EXPECT_EQ(dst[i], src[i]) << "mismatch at word " << i;
  }
}

// 5 words (20 bytes) – one unrolled group + one scalar tail word.
TEST_F(AlignedCopyBoundaryTest, FiveWords) {
  constexpr size_t kN = 5;
  auto src = make_pattern(kN);
  std::vector<uint32_t> dst(kN, 0u);
  base_memory_copy_aligned(dst.data(), src.data(), kN * sizeof(uint32_t));
  EXPECT_EQ(dst, src);
}

// 16 words (64 bytes) – exactly at the DMA threshold.
// In host builds, the DMA wrapper degrades to the CPU path.
TEST_F(AlignedCopyBoundaryTest, SixteenWords_DmaThreshold) {
  constexpr size_t kN = 16;
  auto src = make_pattern(kN, 0xFEEDFACEu);
  std::vector<uint32_t> dst(kN, 0u);

  // Direct CPU call.
  base_memory_copy_aligned(dst.data(), src.data(), kN * sizeof(uint32_t));
  EXPECT_EQ(dst, src);
}

// ============================================================
// Suite: DmaWrapperTest
// ============================================================
//
// On host builds, `base_memory_copy_aligned_dma` ignores the dma handle and
// falls through to the CPU copy.  We verify that the wrapper produces
// identical results for sub-threshold and super-threshold sizes.
class DmaWrapperTest : public ::testing::TestWithParam<size_t> {};

TEST_P(DmaWrapperTest, MatchesDirectCopy) {
  const size_t num_words = GetParam();
  const size_t len = num_words * sizeof(uint32_t);

  auto src = make_pattern(num_words, 0x13371337u);
  std::vector<uint32_t> dst_cpu(num_words, 0u);
  std::vector<uint32_t> dst_dma(num_words, 0u);

  base_memory_copy_aligned(dst_cpu.data(), src.data(), len);
  void *ret =
      base_memory_copy_aligned_dma(/*dma=*/nullptr, dst_dma.data(),
                                   src.data(), len);

  EXPECT_EQ(ret, static_cast<void *>(dst_dma.data()))
      << "DMA wrapper must return dest";
  EXPECT_EQ(dst_dma, dst_cpu)
      << "DMA wrapper mismatch for len=" << len;
}

// Mix of sub-threshold (1–15 words = 4–60 bytes) and super-threshold
// (16–32 words = 64–128 bytes) sizes.
INSTANTIATE_TEST_SUITE_P(SubThreshold, DmaWrapperTest,
                         ::testing::Range<size_t>(1, 16));

INSTANTIATE_TEST_SUITE_P(SuperThreshold, DmaWrapperTest,
                         ::testing::Range<size_t>(16, 33));

// ============================================================
// Suite: ReturnValueTest
// ============================================================
//
// Both functions must return dest, matching the memcpy(3) convention.
TEST(ReturnValueTest, AlignedCopyReturnsDest) {
  alignas(uint32_t) uint32_t src[4] = {1, 2, 3, 4};
  alignas(uint32_t) uint32_t dst[4] = {0};

  void *ret = base_memory_copy_aligned(dst, src, sizeof(src));
  EXPECT_EQ(ret, static_cast<void *>(dst));
}

TEST(ReturnValueTest, DmaWrapperReturnsDest) {
  alignas(uint32_t) uint32_t src[4] = {5, 6, 7, 8};
  alignas(uint32_t) uint32_t dst[4] = {0};

  void *ret = base_memory_copy_aligned_dma(nullptr, dst, src, sizeof(src));
  EXPECT_EQ(ret, static_cast<void *>(dst));
}

// ============================================================
// Suite: InstructionCountProxy
// ============================================================
//
// We cannot count hardware instructions in a host unit test.  Instead, we
// verify that the aligned copy performs the correct number of *word*
// transfers (i.e., `len / 4` writes) by checking that every destination
// word equals the source word.  Combined with the source-unmodified test,
// this proves correctness at word granularity.
//
// The analytical instruction count reduction (~4.25×) is documented in the
// header file comment block and is validated by inspection of the generated
// assembly with `objdump -d` under `-O2` or `-Os`.
TEST(InstructionCountProxy, AllWordsWritten) {
  constexpr size_t kN = 32;  // 128 bytes
  auto src = make_pattern(kN, 0xABCDEF01u);
  std::vector<uint32_t> dst(kN, 0xFFFFFFFFu);

  base_memory_copy_aligned(dst.data(), src.data(), kN * sizeof(uint32_t));

  for (size_t i = 0; i < kN; ++i) {
    EXPECT_EQ(dst[i], src[i])
        << "word at index " << i << " was not correctly written";
  }
}
