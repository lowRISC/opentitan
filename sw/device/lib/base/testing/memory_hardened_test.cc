// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory_hardened.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"

namespace {
using ::testing::Test;

class MemoryHardenedTest : public Test {};

/* Buffers used for testing. */
uint32_t s_buf[768];
uint32_t s2_buf[768];
uint32_t d_buf[768];

/**
 * The 32 bit LFSR whose maximum length feedback polynomial is represented
 * as X^32 + X^22 + X^2 + X^1 + 1 will produce 2^32-1 PN sequence.
 * This LFSR can be initialized with 0,  but can't be initialized with
 * 0xFFFFFFFF
 */
static uint32_t lfsr32(uint32_t seed) {
  uint32_t mask = (-((int32_t)seed >= 0)) & 0xC0000401;
  return (seed << 1) ^ mask;
}

/**
 * Testing shuffled memory operations is a bit tricky and requires known
 * patterns to be sure that data was copied as expected. Regular patterns
 * don't work as logical errors may result in copying same data twice in
 * different location or in wrong location.
 *
 * Use pseudo-random patterns with provided seed. Exact copy should have
 * all elements equal. Wipes should result in most elements not equal.
 */

/* Fill buffer with pseudo-random pattern. */
static void fill_rand(void *buf, uint32_t seed, size_t len) {
  uint8_t *ptr = (uint8_t *)buf;

  while (len) {
    size_t remaining_seed = sizeof(seed);
    uint32_t c_seed = seed;
    seed = lfsr32(seed);

    while (remaining_seed != 0 && len > 0) {
      *ptr = c_seed & 0xff;
      c_seed >>= 8;
      ptr++;
      len--;
      remaining_seed--;
    };
  }
}

/* Count matches with specific pseudo-random pattern. */
static size_t count_rand_equal(const void *buf, uint32_t seed, size_t len) {
  size_t count = 0;
  uint8_t *ptr = (uint8_t *)buf;

  while (len) {
    size_t remaining_seed = sizeof(seed);
    uint32_t c_seed = seed;
    seed = lfsr32(seed);

    while (remaining_seed != 0 && len > 0) {
      if (*ptr == (c_seed & 0xff))
        count++;
      c_seed >>= 8;
      ptr++;
      len--;
      remaining_seed--;
    };
  }
  return count;
}

/* Count matches if dest = src1 ^ src2. */
static size_t count_xored(const void *dest, const void *src1, const void *src2,
                          size_t len) {
  size_t count = 0;
  const uint8_t *destb8 = (uint8_t *)dest;
  const uint8_t *src1b8 = (uint8_t *)src1;
  const uint8_t *src2b8 = (uint8_t *)src2;

  while (len) {
    count += (*destb8 == (*src1b8 ^ *src2b8));
    len--;
    destb8++;
    src1b8++;
    src2b8++;
  }
  return count;
}

TEST_F(MemoryHardenedTest, ShuffledChecksum) {
  s_buf[0] = 1;
  s_buf[1] = 2;
  s_buf[2] = 3;
  s_buf[3] = 4;
  EXPECT_EQ(shuffled_checksum(s_buf, 0, 4, 1431655765), 10);
  d_buf[0] = 5;
  d_buf[1] = 6;
  d_buf[2] = 7;
  d_buf[3] = 8;
  EXPECT_EQ(shuffled_checksum(s_buf, d_buf, 4, 1431655765), 36);
}

TEST_F(MemoryHardenedTest, ShuffledMemcpySmokeTest) {
  fill_rand(s_buf, 0, sizeof(s_buf));
  EXPECT_EQ(count_rand_equal(s_buf, 0, sizeof(s_buf)), sizeof(s_buf));
  fill_rand(d_buf, 10, sizeof(s_buf));
  EXPECT_EQ(count_rand_equal(d_buf, 10, sizeof(d_buf)), sizeof(d_buf));
  EXPECT_NE(count_rand_equal(d_buf, 0, sizeof(d_buf)), sizeof(d_buf));

  /* smoke test shuffled_memcpy()  works */
  EXPECT_EQ(shuffled_memcpy(d_buf, s_buf, sizeof(d_buf), 1717986918),
            kHardenedBoolTrue);
  EXPECT_EQ(count_rand_equal(d_buf, 0, sizeof(d_buf)), sizeof(d_buf));

  fill_rand(s_buf, 0, sizeof(s_buf));
  fill_rand(d_buf, 10, sizeof(d_buf));
  EXPECT_EQ(shuffled_memcpy(d_buf, s_buf, 7, 1717986918), kHardenedBoolTrue);
  EXPECT_EQ(count_rand_equal(d_buf, 0, 7), 7);
}

// Test various memory sizes, aligned.
TEST_F(MemoryHardenedTest, ShuffledMemcpyTestAligned) {
  uint32_t seed = 1717986918;
  for (size_t i = 1; i <= sizeof(d_buf); i++) {
    /* first, clean up */
    fill_rand(s_buf, 0x11111111, sizeof(s_buf));
    fill_rand(s_buf, 0x23456789, i);
    fill_rand(d_buf, 0x33333333, i);

    EXPECT_EQ(shuffled_memcpy(d_buf, s_buf, i, seed), kHardenedBoolTrue);
    EXPECT_EQ(count_rand_equal(d_buf, 0x23456789, i), i);
    EXPECT_EQ(memcmp_checked(d_buf, s_buf, i), kHardenedBoolTrue);

    d_buf[((i - 1) / sizeof(uint32_t))] ^= 0x01010101;
    EXPECT_EQ(shuffled_memcmp(d_buf, s_buf, i, seed), kHardenedBoolFalse);
    EXPECT_EQ(memcmp_checked(d_buf, s_buf, i), kHardenedBoolFalse);

    seed = lfsr32(seed);
    EXPECT_EQ(wipe_checked(d_buf, i, seed), kHardenedBoolTrue);

    /* we shouldn't expect many bytes unchanged */
    EXPECT_LE(count_rand_equal(d_buf, 0x23456789, i), (i >> 1));
    EXPECT_EQ(memcmp_checked(d_buf, s_buf, i), kHardenedBoolFalse);
  }
}

// Test various memory sizes, unaligned
TEST_F(MemoryHardenedTest, ShuffledMemTestUnaligned) {
  uint32_t seed = 1717986918;
  for (size_t sa = 0; sa < sizeof(uintptr_t); sa++)
    for (size_t da = 0; da < sizeof(uintptr_t); da++) {
      uint8_t *d = (uint8_t *)d_buf;
      uint8_t *s = (uint8_t *)s_buf;

      size_t copy_size = sizeof(d_buf) - sa - da;

      /* make tests a bit faster for expected byte copies */
      if (sa != da) {
        copy_size >>= 2;
      }

      d += da;
      s += sa;
      for (size_t i = 1; i <= copy_size; i += 13) {
        /* first, clean up */
        fill_rand(s, 0x11111111, copy_size);
        fill_rand(s, 0x12345678, i);
        fill_rand(d, 0x33333333, i);

        EXPECT_EQ(shuffled_memcpy(d, s, i, seed), kHardenedBoolTrue);
        EXPECT_EQ(count_rand_equal(d, 0x12345678, i), i);

        fill_rand(d, 0x33333333, i);
        EXPECT_EQ(memcpy_checked(d, s, i), kHardenedBoolTrue);
        EXPECT_EQ(count_rand_equal(d, 0x12345678, i), i);

        EXPECT_EQ(memcmp_checked(d, s, i), kHardenedBoolTrue);
        EXPECT_EQ(shuffled_memcmp(d, s, i, seed), kHardenedBoolTrue);

        d[i - 1] ^= 1;
        EXPECT_EQ(shuffled_memcmp(d, s, i, seed), kHardenedBoolFalse);
        EXPECT_EQ(memcmp_checked(d, s, i), kHardenedBoolFalse);

        seed = lfsr32(seed);
        EXPECT_EQ(wipe_checked(d, i, 0x33333333), kHardenedBoolTrue);

        /* we shouldn't expect many bytes unchanged */
        EXPECT_LE(count_rand_equal(d, 0x12345678, i), (i >> 1));
        EXPECT_EQ(memcmp_checked(d, s, i), kHardenedBoolFalse);
        EXPECT_EQ(shuffled_memcmp(d, s, i, seed), kHardenedBoolFalse);
      }
    }
}

TEST_F(MemoryHardenedTest, ShuffledMemcpy32TestAligned) {
  const uint32_t max_size = 12;
  uint32_t seed = 1;

  fill_rand(s_buf, 0x11111111, sizeof(s_buf));
  EXPECT_EQ(count_rand_equal(s_buf, 0x11111111, sizeof(s_buf)), sizeof(s_buf));
  fill_rand(d_buf, 0x22222222, sizeof(s_buf));
  EXPECT_EQ(count_rand_equal(d_buf, 0x22222222, sizeof(d_buf)), sizeof(d_buf));
  EXPECT_NE(count_rand_equal(d_buf, 0x11111111, sizeof(d_buf)), sizeof(d_buf));

  for (size_t i = 0; i <= max_size; i++) {
    for (size_t j = 0; j < 100; j++) {
      /* first, clean up */
      fill_rand(s_buf, 0x11111111, sizeof(s_buf));
      fill_rand(s_buf, 0x22222222, i * sizeof(uint32_t));
      fill_rand(d_buf, 0x33333333, i * sizeof(uint32_t));

      EXPECT_EQ(shuffled_memcpy32(d_buf, s_buf, i, seed), kHardenedBoolTrue);

      EXPECT_EQ(count_rand_equal(d_buf, 0x22222222, i * sizeof(uint32_t)),
                i * sizeof(uint32_t));

      seed = lfsr32(seed);
    }
  }
}

TEST_F(MemoryHardenedTest, ShuffledReverse32) {
  s_buf[0] = 0x04030201;
  s_buf[1] = 0x08070605;
  s_buf[2] = 0x0c0b0a09;
  s_buf[3] = 0x100f0e0d;
  s_buf[4] = 0x14131211;
  EXPECT_EQ(shuffled_reverse32(s_buf, 5, 1431655765), kHardenedBoolTrue);
  EXPECT_EQ(s_buf[0], 0x11121314);
  EXPECT_EQ(s_buf[4], 0x01020304);
  EXPECT_EQ(s_buf[1], 0x0d0e0f10);
  EXPECT_EQ(s_buf[2], 0x090a0b0c);
  EXPECT_EQ(s_buf[3], 0x05060708);
}

TEST_F(MemoryHardenedTest, MemxorTestUnaligned) {
  for (size_t sa = 0; sa < sizeof(uintptr_t); sa++)
    for (size_t da = 0; da < sizeof(uintptr_t); da++) {
      uint8_t *d = (uint8_t *)d_buf;
      uint8_t *s1 = (uint8_t *)s_buf;
      uint8_t *s2 = (uint8_t *)s2_buf;

      size_t copy_size = sizeof(d_buf) - sa - da;

      /* make tests a bit faster for expected byte copies */
      if (sa != da) {
        copy_size >>= 2;
      }

      d += da;
      s1 += sa;
      s2 += sa;

      for (size_t i = 1; i <= copy_size; i += 13) {
        /* fill with distinct patterns */
        fill_rand(s1, 0x12345678, i);
        fill_rand(s2, 0xA8B7A566, i);
        fill_rand(d, 0x33333333, i);

        EXPECT_NE(count_xored(d, s1, s2, i), i);
        EXPECT_EQ(memxor_checked(d, s1, s2, i), kHardenedBoolTrue);
        EXPECT_EQ(count_xored(d, s1, s2, i), i);
      }
    }
}

}  // namespace
