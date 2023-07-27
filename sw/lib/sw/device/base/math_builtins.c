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

// Linker aliases for libgcc symbols.
#ifdef OT_PLATFORM_RV32

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
