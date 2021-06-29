// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_

#include <stdint.h>

#include "sw/device/lib/base/stdasm.h"

/**
 * @file
 * @brief Data Types for use in Hardened Code.
 */

/**
 * This is a boolean type for use in hardened contexts.
 *
 * The intention is that this is used instead of `<stdbool.h>`'s #bool, where a
 * higher hamming distance is required between the truthy and the falsey value.
 *
 * The values below were chosen at random, with some specific restrictions. They
 * have a Hamming Distance of 8, and they are 11-bit values so they can be
 * materialized with a single instruction on RISC-V. They are also specifically
 * not the complement of each other.
 */
typedef enum hardened_bool {
  /**
   * The truthy value, expected to be used like #true.
   */
  kHardenedBoolTrue = 0x739u,
  /**
   * The falsey value, expected to be used like #false.
   */
  kHardenedBoolFalse = 0x1d4u,
} hardened_bool_t;

/**
 * Launders the 32-bit value `val`.
 *
 * `launder32()` returns a value identical to the input, while introducing an
 * optimization barrier that prevents the compiler from learning new information
 * about the original value, based on operations on the laundered value. This
 * does not work the other way around: some information that the compiler has
 * already learned about the value may make it through; this last caveat is
 * explained below.
 *
 * In some circumstances, it is desirable to introduce a redundant (from the
 * compiler's perspective) operation into the instruction stream to make it less
 * likely that hardware faults will result in critical operations being
 * bypassed. Laundering makes it possible to insert such duplicate operations,
 * while blocking the compiler's attempts to delete them through dead code
 * elimination.
 *
 * For example, in the following code, a compiler would fold `CHECK()` away,
 * since dataflow analysis could tell it that `x` is always zero, allowing it to
 * deduce that `x == 0` -> `0 == 0` -> `true`. It then deletes the `CHECK(true)`
 * as dead code.
 * ```
 * if (x == 0) {
 *   CHECK(x == 0);
 * }
 * ```
 *
 * If we believe that an attacker can glitch the chip to skip the first branch,
 * this assumption no longer holds. We can use laundering to prevent LLVM from
 * learning that `x` is zero inside the block:
 * ```
 * if (launder32(x) == 0) {
 *   CHECK(x == 0);
 * }
 * ```
 *
 * Note that this operation is order sensitive: while we can stop the compiler
 * from learning new information, it is very hard to make it forget in some
 * cases. If we had instead written
 * ```
 * if (x == 0) {
 *   CHECK(launder32(x) == 0);
 * }
 * ```
 * then it would be entitled to rewrite this into `launder32(0) == 0`.
 * Although it can't make the deduction that this is identically true, because
 * `launder32()` is the identity function, this behaves like `0 == 0` at
 * runtime. For example, a completely valid lowering of this code is
 * ```
 * bnez a0, else
 * mv a0, zero
 * bnez a0, shutdown
 * // ...
 * ```
 *
 * Even pulling the expression out of the branch as `uint32_t y = launder32(x);`
 * doesn't work, because the compiler may chose to move the operation into the
 * branch body. Thus, we need to stop it from learning that `x` is zero in the
 * first place.
 *
 * ---
 *
 * In general, this intrinsic should *only* be used on values that the compiler
 * doesn't already know anything interesting about. The precise meaning of this
 * can be subtle, since inlining can easily foil pessimization. Uses of this
 * function must be carefully reviewed, and commented with justification and an
 * explanation of what information it is preventing access to, and what ambient
 * invariants it relies on.
 *
 * This function makes no guarantees: it is only intended to help harden code.
 * It does not remove the need to carefully verify that the correct
 * instruction-level invariants are upheld in the final release.
 *
 * This operation *does not* introduce a sequence point: a compiler may move it
 * anywhere between where its input is last modified or its output is first
 * moved. This can include moving through different nodes in the control flow
 * graph. The location of the laundering operation must be determined
 * *exclusively* by its position in the expression dependency graph.
 *
 * Other examples of laundering use-cases should be listed here as they become
 * apparent.
 *
 * * Obscuring loop completion. It may be useful to prevent a compiler from
 *   learning that a particular loop is guaranteed to complete. The most
 *   straightforward way to do this is to launder the loop increment: replace
 *   `++i` with `i = launder32(i) + 1`. This is helpful for preventing the
 *   compiler from learning that the loop executes in a particular order, and
 *   foiling unroll/unroll-and-jam optimizations. It also prevents the compiler
 *   from learning that the loop counter was saturated. However, if the exit
 *   condition is `i < len`, the compiler will learn that `i >= len` outside the
 *   loop.
 *
 *   Laundering just the exit comparison, `launder32(i) < len`, will still allow
 *   the compiler to deduce that the loop is traversed in linear order, but it
 *   will not learn that `i >= len` outside the loop. Laundering both loop
 *   control expressions may be necessary in some cases.
 *
 * * Assigning a literal to a value without the compiler learning about
 *   that literal value. `x = launder32(0);` zeros `x`, but the compiler
 *   cannot replace all uses of it with a constant `0`. Note that
 *   `x = launder32(x);` does not prevent knowledge the compiler already has
 *   about `x` from replacing it with a constant in `launder32()`.
 *
 * * Preventing operations from being re-associated. The compiler is entitled
 *   to rewrite `x ^ (y ^ z)` into `(x ^ y) ^ z`, but cannot do the same with
 *   `x ^ launder32(y ^ z)`. No operations commute through `launder32()`.
 *
 * * Preventing dead-code elimination. The compiler cannot delete the
 *   unreachable expression `if (launder32(false)) { foo(); }`. However, the
 *   branch will never be executed in an untampered instruction stream.
 *
 * @param val A 32-bit integer to launder.
 * @return A 32-bit integer which will happen to have the same value as `val` at
 *         runtime.
 */
inline uint32_t launder32(uint32_t val) {
  // NOTE: This implementation is LLVM-specific, and should be considered to be
  // a no-op in every other compiler. For example, GCC has in the past peered
  // into the insides of assembly blocks.
  //
  // LLVM cannot see through assembly blocks, and must treat this as a black
  // box. Similar tricks are employed in other security-sensitive code-bases,
  // such as https://boringssl-review.googlesource.com/c/boringssl/+/36484.
  //
  // It is *not* marked as volatile, since reordering is not desired; marking it
  // as volatile does make some laundering operations suddenly start working
  // spuriously, which is entirely dependent on how excited LLVM is about
  // reordering things. To avoid this trap, we do not mark as volatile and
  // instead require that reordering be prevented through careful sequencing of
  // statements.
  //
  // The +r constraint tells the compiler that this is an "inout" parameter: it
  // means that not only does the black box depend on `val`, but it also mutates
  // it in an unspecified way. This ensures that the laundering operation occurs
  // in the right place in the dependency ordering.
  asm("" : "+r"(val));
  return val;
}

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
