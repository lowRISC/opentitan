// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Implementations of libgcc-style polyfills for arithmetic.
 *
 * This file has no header, since its functions should not be called directly;
 * the compiler will generate calls into them as needed.
 *
 * The functions have names like `_ot_builtin_*`, rather than their libgcc
 * names, so that they can coexist with libgcc/libcompiler-rt on the host-side
 * for the purpose of unit tests. The linker aliases for the libgcc names only
 * exist on the device-side.
 *
 * See https://github.com/llvm/llvm-project/tree/main/compiler-rt/lib/builtins
 * for a detailed specification of the ABI we implement in this file.
 *
 * The provided functions here are:
 * - 64-bit shifts.
 * - 32-bit popcount, parity, bswap, clz, ctz, and find first.
 *
 * Although the RISC-V B extension provides instructions for some ofthese, we
 * currently do not require using a Clang that is aware of how to codegen them,
 * so LLVM may choose to emit libgcc polyfill symbols (like the following)
 * instead. Once we mandate such a Clang, they should be removed.
 */

#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/macros.h"

/**
 * Helper type for fussing with the upper and lower halves of an i64.
 *
 * This is necessary to avoid accidentally calling into the shift polyfills
 * inside of their implementations.
 */
typedef union u32x2 {
  struct {
    uint32_t lo;
    union {
      uint32_t hi;
      int32_t hi_signed;
    };
  };
  int64_t full;
} u32x2_t;

int64_t _ot_builtin_lshift_i64(int64_t val, int32_t shift) {
  if (shift == 0) {
    return val;
  }

  u32x2_t word = {.full = val};

  // When doing a big shift, we have
  //
  // aaaa'aaaa'bbbb'bbbb
  // bbbb'bb00'0000'0000
  if (shift >= 32) {
    word.hi = word.lo << (shift - 32);
    word.lo = 0;
    return word.full;
  }

  // When doing a small shift, we have
  //
  // aaaa'aaaa'bbbb'bbbb
  // aaaa'aabb'bbbb'bb00
  word.hi <<= shift;
  word.hi |= word.lo >> (32 - shift);
  word.lo <<= shift;
  return word.full;
}

int64_t _ot_builtin_rshift_i64(int64_t val, int32_t shift) {
  if (shift == 0) {
    return val;
  }

  u32x2_t word = {.full = val};

  // When doing a big shift, we have
  //
  // aaaa'aaaa'bbbb'bbbb
  // 0000'0000'00aa'aaaa
  if (shift >= 32) {
    word.lo = word.hi >> (shift - 32);
    word.hi = 0;
    return word.full;
  }

  // When doing a small shift, we have
  //
  // aaaa'aaaa'bbbb'bbbb
  // 00aa'aaaa'aabb'bbbb
  word.lo >>= shift;
  word.lo |= word.hi << (32 - shift);
  word.hi >>= shift;

  return word.full;
}

int64_t _ot_builtin_ashift_i64(int64_t val, int32_t shift) {
  if (shift == 0) {
    return val;
  }

  u32x2_t word = {.full = val};

  // When doing a big shift, we have
  //
  // aaaa'aaaa'bbbb'bbbb
  // ssss'ssss'ssaa'aaaa
  //
  // where s is sign bits.
  if (shift >= 32) {
    word.lo = word.hi_signed >> (shift - 32);
    word.hi_signed >>= 31;
    return word.full;
  }

  // When doing a small shift, we have
  //
  // aaaa'aaaa'bbbb'bbbb
  // ssaa'aaaa'aabb'bbbb
  //
  // where s is sign bits.
  word.lo >>= shift;
  word.lo |= word.hi << (32 - shift);
  word.hi_signed >>= shift;

  return word.full;
}

int32_t _ot_builtin_bswap_i32(int32_t val) {
  uint32_t x = val;
  return (((x & 0xff000000) >> 24) | ((x & 0x00ff0000) >> 8) |
          ((x & 0x0000ff00) << 8) | ((x & 0x000000ff) << 24));
}

int _ot_builtin_popcount_i32(int32_t val) {
  // Standard "sum of interleaved bits" algorithm for popcount.
  //
  // Each iteration, we take an array of [N x iM], mask them out into arrays of
  // even and odd entries, shift the even one so it lines up with the odd one,
  // and add them, making a [N/2 x i(M * 2)]. We start from a [32 x i1] and
  // work towards a [1 x i32].
  uint32_t i1x32 = val;
  uint32_t i2x16 = (i1x32 & 0x55555555) + ((i1x32 >> 1) & 0x55555555);
  uint32_t i4x8 = (i2x16 & 0x33333333) + ((i2x16 >> 2) & 0x33333333);
  uint32_t i8x4 = (i4x8 & 0x0f0f0f0f) + ((i4x8 >> 4) & 0x0f0f0f0f);
  uint32_t i16x2 = (i8x4 & 0x00ff00ff) + ((i8x4 >> 8) & 0x00ff00ff);
  uint32_t i32x1 = (i16x2 & 0xffff) + ((i16x2 >> 16) & 0xffff);

  // i32x1 will never be greater than 32, so it can be safely converted.
  return (int)i32x1;
}

int _ot_builtin_parity_i32(int32_t val) {
  // Parity can be implemented as XOR of all bits.
  uint32_t x = val;
  for (int i = 16; i > 0; i /= 2) {
    x ^= x >> i;
  }
  return x & 1;
}

// NOTE: val != 0 is a precondition of the ABI.
int _ot_builtin_ctz_i32(int32_t val) {
  // Binary search, adapted from Ch2 of Hacker's Delight.
  uint32_t x = val;
  int count = 0;
  for (int i = 16; i > 0; i /= 2) {
    int32_t mask = (1u << i) - 1;
    if ((x & mask) == 0) {
      count += i;
      x >>= i;
    }
  }
  return count;
}

// NOTE: val != 0 is a precondition of the ABI.
int _ot_builtin_clz_i32(int32_t val) {
  // Binary search, adapted from Ch2 of Hacker's Delight.
  uint32_t x = val;
  int count = 0;
  for (int i = 16; i > 0; i /= 2) {
    int32_t mask = ((1u << i) - 1) << (32 - i);
    if ((x & mask) == 0) {
      count += i;
      x <<= i;
    }
  }
  return count;
}

int _ot_builtin_find_first_i32(int32_t val) {
  if (val == 0) {
    return 0;
  }

  // LSB is bit index 1.
  return _ot_builtin_ctz_i32(val) + 1;
}

// Linker aliases for libgcc symbols.
#ifdef OT_PLATFORM_RV32
OT_WEAK
OT_ALIAS("_ot_builtin_lshift_i64")
int64_t __ashldi3(int64_t val, int32_t shift);
OT_WEAK
OT_ALIAS("_ot_builtin_rshift_i64")
int64_t __lshrdi3(int64_t val, int32_t shift);
OT_WEAK
OT_ALIAS("_ot_builtin_ashift_i64")
int64_t __ashrdi3(int64_t val, int32_t shift);

OT_WEAK
OT_ALIAS("_ot_builtin_bswap_i32")
int32_t __bswapsi2(int32_t val);
OT_WEAK
OT_ALIAS("_ot_builtin_popcount_i32")
int __popcountsi2(int32_t val);
OT_WEAK
OT_ALIAS("_ot_builtin_parity_i32")
int __paritysi2(int32_t val);

OT_WEAK
OT_ALIAS("_ot_builtin_ctz_i32")
int __ctzsi2(int32_t val);
OT_WEAK
OT_ALIAS("_ot_builtin_clz_i32")
int __clzsi2(int32_t val);
OT_WEAK
OT_ALIAS("_ot_builtin_find_first_i32")
int __ffssi2(int32_t val);

extern noreturn void
_ot_builtin_div64_intentionally_not_implemented_see_pull_11451(void);

// "Trap" polyfills to catch uses of u64 divsion and display an "error" via
// the name of an undefined symbol.
//
// Of course, this depends on people linking this file in... but hopefully it
// is sufficiently pervasive that that won't be an issue; at any rate, it means
// people will land somewhere when they grep for __udivdi3 and friends.
OT_WEAK int64_t __divdi3(int64_t a, int64_t b) {
  _ot_builtin_div64_intentionally_not_implemented_see_pull_11451();
}
OT_WEAK uint64_t __udivdi3(uint64_t a, uint64_t b) {
  _ot_builtin_div64_intentionally_not_implemented_see_pull_11451();
}
OT_WEAK int64_t __moddi3(int64_t a, int64_t b) {
  _ot_builtin_div64_intentionally_not_implemented_see_pull_11451();
}
OT_WEAK uint64_t __umoddi3(uint64_t a, uint64_t b) {
  _ot_builtin_div64_intentionally_not_implemented_see_pull_11451();
}
OT_WEAK int64_t __divmoddi4(int64_t a, int64_t b, int64_t *rem) {
  _ot_builtin_div64_intentionally_not_implemented_see_pull_11451();
}
OT_WEAK uint64_t __udivmoddi4(uint64_t a, uint64_t b, uint64_t *rem) {
  _ot_builtin_div64_intentionally_not_implemented_see_pull_11451();
}
#endif  // OT_PLATFORM_RV32
