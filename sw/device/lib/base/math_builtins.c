// Copyright lowRISC contributors (OpenTitan project).
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
    word.lo = (uint32_t)(word.hi_signed >> (shift - 32));
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

extern noreturn void
_ot_builtin_div64_intentionally_not_implemented_see_pull_11451(void);

// "Trap" polyfills to catch uses of u64 divsion and display an "error" via
// the name of an undefined symbol.
//
// Of course, this depends on people linking this file in... but hopefully it
// is sufficiently pervasive that won't be an issue; at any rate, it means
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
