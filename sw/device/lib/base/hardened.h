// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_

#include <stdint.h>

#include "sw/device/lib/base/hardened_asm.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"

/**
 * @file
 * @brief Data Types for use in Hardened Code.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

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
  kHardenedBoolTrue = HARDENED_BOOL_TRUE,
  /**
   * The falsey value, expected to be used like #false.
   */
  kHardenedBoolFalse = HARDENED_BOOL_FALSE,
} hardened_bool_t;

/**
 * A byte-sized hardened boolean.
 *
 * This type is intended for cases where a byte-sized hardened boolean is
 * required, e.g. for the entries of the `CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN`
 * OTP item.
 *
 * The values below were chosen to ensure that the hamming difference between
 * them is greater than 5 and they are not bitwise complements of each other.
 */
typedef enum hardened_byte_bool {
  /**
   * The truthy value.
   */
  kHardenedByteBoolTrue = HARDENED_BYTE_BOOL_TRUE,
  /**
   * The falsy value.
   */
  kHardenedByteBoolFalse = HARDENED_BYTE_BOOL_FALSE,
} hardened_byte_bool_t;

/*
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
 * Suppose we have a pure-C `CHECK()` macro that does a runtime-assert.
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
 * Note that, in spite of `HARDENED_CHECK` being written in assembly, it is
 * still vulnerable to certain inimical compiler optimizations. For example,
 * `HARDENED_CHECK_EQ(x, 0)` can be written to `HARDENED_CHECK_EQ(0, 0)`.
 * Although the compiler cannot delete this code, it will emit the nonsensical
 * ```
 *   beqz zero, continue
 *   unimp
 * continue:
 * ```
 * effectively negating the doubled condition.
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
 * @return A 32-bit integer which will *happen* to have the same value as `val`
 *         at runtime.
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
  // # "To volatile or not to volatile, that is the question."
  // Naively, this snippet would not be marked volatile, since we do not care
  // about reordering. However, there are rare optimizations that can result
  // in "miscompilation" of this primitive. For example, if the argument is
  // a complex expression, we get something like the following Godbolt:
  // https://godbolt.org/z/c7M7Yr7Yo.
  //
  // This is not actually a miscompilation: LLVM is treating the asm
  // statement as behaving like a random oracle determined entirely by its
  // arguments; therefore, it is entitled to deduplicate both occurences of
  // `LaunderPure(y)` (in this particular case, from bisecting the passes,
  // it appears to happen during register allocation).
  //
  // We work around this by marking the inline asm volatile.
  //
  // Alternatively, we could add a "nonce" to the inline asm that has been
  // tainted by a volatile asm operation. This has the benefit that the input
  // does not need to happen-before the volatile operation, and can be
  // arbitrarily reordered, while ensuring that no call of launder32() is
  // "pure" in the deduplication sense. I.e.:
  //
  //   uint32_t nonce;
  //   asm volatile("" : "=r"(nonce));
  //   asm("" : "+r"(val) : "r"(nonce));
  //
  // At the time of writing, it seems preferable to have something we know is
  // correct rather than being overly clever; this is recorded here in case
  // the current implementation is unsuitable and we need something more
  // carefully tuned.
  //
  // This comment was formerly present to justify the lack of volatile. It is
  // left behind as a warning to not try to remove it without further careful
  // analysis.
  // > It is *not* marked as volatile, since reordering is not desired; marking
  // > it volatile does make some laundering operations suddenly start working
  // > spuriously, which is entirely dependent on how excited LLVM is about
  // > reordering things. To avoid this trap, we do not mark as volatile and
  // > instead require that reordering be prevented through careful sequencing
  // > of statements.

  // The +r constraint tells the compiler that this is an "inout" parameter: it
  // means that not only does the black box depend on `val`, but it also mutates
  // it in an unspecified way.
  asm volatile("" : "+r"(val));
  return val;
}

/**
 * Launders the pointer-sized value `val`.
 *
 * See `launder32()` for detailed semantics.
 *
 * @param val A 32-bit integer to launder.
 * @return A 32-bit integer which will happen to have the same value as `val` at
 *         runtime.
 */
inline uintptr_t launderw(uintptr_t val) {
  asm volatile("" : "+r"(val));
  return val;
}

/**
 * Creates a reordering barrier for `val`.
 *
 * `barrier32()` takes an argument and discards it, while introducing an
 * "impure" dependency on that value. This forces the compiler to schedule
 * instructions such that the intermediate `val` actually appears in a
 * register. Because it is impure, `barrier32()` operations will not be
 * reordered past each other or MMIO operations, although they can be reordered
 * past functions if LTO inlines them.
 *
 * Most compilers will try to reorder arithmetic operations in such a way
 * that they form large basic blocks, since modern microarchitectures can
 * take advantage of instruction-level parallelism. Unfortunately, this means
 * that instructions that we want to interleave with other instructions are
 * likely to get separated; this includes static interleavings,
 * loop-invariant code motion, and some kinds of unroll-and-jam.
 *
 * For example, given
 *
 * ```
 * uint32_t product = 5;
 *
 * foo();
 * product *= product;
 * foo();
 * product *= product;
 * foo();
 * product *= product;
 * ```
 *
 * A compiler will likely reorder this as
 *
 * ```
 * uint32_t product = 5;
 *
 * foo();
 * foo();
 * foo();
 * product *= product;
 * product *= product;
 * product *= product;
 * ```
 *
 * The compiler is further entitled to constant-propagate `product`.
 * `barrier32()` can be used to avoid this:
 *
 * ```
 * // NB: the initial value of `product` is laundered to prevent
 * // constant propagation, but only because it is a compile-time
 * // constant. Laundering the intermediates would also work.
 * uint32_t product = launder32(5);
 * barrier32(product);
 *
 * barrier32(foo());
 * product *= product;
 * barrier32(product);
 *
 * barrier32(foo());
 * product *= product;
 * barrier32(product);
 *
 * barrier32(foo());
 * product *= product;
 * barrier32(product);
 * ```
 *
 * Note that we must place barriers on the result of the function calls,
 * too, so that the compiler believes that there is a potential dependency
 * between the return value of the function, and the followup value of
 * `product`.
 *
 * This is also useful for avoiding loop reordering:
 *
 * ```
 * for (int i = 0; i != n - 1; i = (i + kPrime) % n) {
 *   barrier32(i);
 *
 *   // Stuff.
 * }
 * ```
 *
 * A sufficiently intelligent compiler might notice that it can linearize this
 * loop; however, the barriers in each loop iteration force a particular order
 * is observed.
 *
 * @param val A value to create a barrier for.
 */
inline void barrier32(uint32_t val) { asm volatile("" ::"r"(val)); }

/**
 * Creates a reordering barrier for `val`.
 *
 * See `barrier32()` for detailed semantics.
 *
 * @param val A value to create a barrier for.
 */
inline void barrierw(uintptr_t val) { asm volatile("" ::"r"(val)); }

/**
 * A constant-time, 32-bit boolean value.
 *
 * Values of this type MUST be either all zero bits or all one bits,
 * representing `false` and `true` respectively.
 *
 * Although it is possible to convert an existing `bool` into a `ct_bool32_t` by
 * writing `-((ct_bool32_t) my_bool)`, we recommend against it
 */
typedef uint32_t ct_bool32_t;

// The formulae below are taken from Hacker's Delight, Chapter 2.
// Although the book does not define them as being constant-time, they are
// branchless; branchless code is always constant-time.
//
// Proofs and references to HD are provided only in the 32-bit versions.
//
// Warren Jr., Henry S. (2013). Hacker's Delight (2 ed.).
//   Addison Wesley - Pearson Education, Inc. ISBN 978-0-321-84268-8.

/**
 * Performs constant-time signed comparison to zero.
 *
 * Returns whether `a < 0`, as a constant-time boolean.
 * In other words, this checks if `a` is negative, i.e., it's sign bit is set.
 *
 * @return `a < 0`.
 */
inline ct_bool32_t ct_sltz32(int32_t a) {
  // Proof. `a` is negative iff its MSB is set;
  // arithmetic-right-shifting by bits(a)-1 smears the sign bit across all
  // of `a`.
  return (uint32_t)(a >> (sizeof(a) * 8 - 1));
}

/**
 * Performs constant-time unsigned ascending comparison.
 *
 * Returns `a < b` as a constant-time boolean.
 *
 * @return `a < b`.
 */
inline ct_bool32_t ct_sltu32(uint32_t a, uint32_t b) {
  // Proof. See Hacker's Delight page 23.
  return ct_sltz32((a & ~b) | ((a ^ ~b) & (a - b)));
}

/**
 * Performs constant-time zero equality.
 *
 * Returns `a == 0` as a constant-time boolean.
 *
 * @return `a == 0`.
 */
inline ct_bool32_t ct_seqz32(uint32_t a) {
  // Proof. See Hacker's Delight page 23.
  // HD gives this formula: `a == b := ~(a-b | b-a)`.
  //
  // Setting `b` to zero gives us
  //   ~(a | -a) -> ~a & ~-a -> ~a & (a - 1)
  // via identities on page 16.
  //
  // This forumula is also given on page 11 for a different purpose.
  return ct_sltz32(~a & (a - 1));
}

/**
 * Performs constant-time equality.
 *
 * Returns `a == b` as a constant-time boolean.
 *
 * @return `a == b`.
 */
inline ct_bool32_t ct_seq32(uint32_t a, uint32_t b) {
  // Proof. a ^ b == 0 -> a ^ a ^ b == a ^ 0 -> b == a.
  return ct_seqz32(a ^ b);
}

/**
 * Performs a constant-time select.
 *
 * Returns `a` if `c` is true; otherwise, returns `b`.
 *
 * This function should be used with one of the comparison functions above; do
 * NOT create `c` using an `if` or `?:` operation.
 *
 * @param c The condition to test.
 * @param a The value to return on true.
 * @param b The value to return on false.
 * @return `c ? a : b`.
 */
inline uint32_t ct_cmov32(ct_bool32_t c, uint32_t a, uint32_t b) {
  // Proof. See Hacker's Delight page 46. HD gives this as a branchless swap;
  // branchless select is a special case of that.

  // `c` must be laundered because LLVM has a strength reduction pass for this
  // exact pattern, but lacking a cmov instruction, it will almost certainly
  // select a branch instruction here.
  return (launder32(c) & a) | (launder32(~c) & b);
}

/**
 * A constant-time, pointer-sized boolean value.
 *
 * Values of this type MUST be either all zero bits or all one bits.
 */
typedef uintptr_t ct_boolw_t;

/**
 * Performs constant-time signed comparison to zero.
 *
 * Returns whether `a < 0`, as a constant-time boolean.
 * In other words, this checks if `a` is negative, i.e., it's sign bit is set.
 *
 * @return `a < 0`.
 */
inline ct_boolw_t ct_sltzw(intptr_t a) {
  return (uintptr_t)(a >> (sizeof(a) * 8 - 1));
}

/**
 * Performs constant-time unsigned ascending comparison.
 *
 * Returns `a < b` as a constant-time boolean.
 *
 * @return `a < b`.
 */
inline ct_boolw_t ct_sltuw(uintptr_t a, uintptr_t b) {
  return ct_sltzw((a & ~b) | ((a ^ ~b) & (a - b)));
}

/**
 * Performs constant-time zero equality.
 *
 * Returns `a == 0` as a constant-time boolean.
 *
 * @return `a == 0`.
 */
inline ct_boolw_t ct_seqzw(uintptr_t a) { return ct_sltzw(~a & (a - 1)); }

/**
 * Performs constant-time equality.
 *
 * Returns `a == b` as a constant-time boolean.
 *
 * @return `a == b`.
 */
inline ct_boolw_t ct_seqw(uintptr_t a, uintptr_t b) { return ct_seqzw(a ^ b); }

/**
 * Performs a constant-time select.
 *
 * Returns `a` if `c` is true; otherwise, returns `b`.
 *
 * This function should be used with one of the comparison functions above; do
 * NOT create `c` using an `if` or `?:` operation.
 *
 * @param c The condition to test.
 * @param a The value to return on true.
 * @param b The value to return on false.
 * @return `c ? a : b`.
 */
inline uintptr_t ct_cmovw(ct_boolw_t c, uintptr_t a, uintptr_t b) {
  return (launderw(c) & a) | (launderw(~c) & b);
}

// Implementation details shared across shutdown macros.
#ifdef OT_PLATFORM_RV32
// This string can be tuned to be longer or shorter as desired, for
// fault-hardening purposes.
#define HARDENED_UNIMP_SEQUENCE_() "unimp; unimp; unimp; unimp;"

#define HARDENED_CHECK_OP_EQ_ "beq"
#define HARDENED_CHECK_OP_NE_ "bne"
#define HARDENED_CHECK_OP_LT_ "bltu"
#define HARDENED_CHECK_OP_GT_ "bgtu"
#define HARDENED_CHECK_OP_LE_ "bleu"
#define HARDENED_CHECK_OP_GE_ "bgeu"

// clang-format off
#define HARDENED_CHECK_(op_, a_, b_) \
  asm volatile(                      \
      op_ " %0, %1, .L_HARDENED_%=;" \
      HARDENED_UNIMP_SEQUENCE_()     \
      ".L_HARDENED_%=:;"             \
      ::"r"(a_), "r"(b_))
// clang-format on

#define HARDENED_TRAP_()                      \
  do {                                        \
    asm volatile(HARDENED_UNIMP_SEQUENCE_()); \
  } while (false)
#else  // OT_PLATFORM_RV32
#include <assert.h>

#define HARDENED_CHECK_OP_EQ_ ==
#define HARDENED_CHECK_OP_NE_ !=
#define HARDENED_CHECK_OP_LT_ <
#define HARDENED_CHECK_OP_GT_ >
#define HARDENED_CHECK_OP_LE_ <=
#define HARDENED_CHECK_OP_GE_ >=

#define HARDENED_CHECK_(op_, a_, b_) assert((uint64_t)(a_)op_(uint64_t)(b_))

#define HARDENED_TRAP_() __builtin_trap()
#endif  // OT_PLATFORM_RV32

/**
 * If the following code is (unexpectedly) reached a trap instruction will be
 * executed.
 */
#define HARDENED_TRAP() HARDENED_TRAP_()

/**
 * Compare two values in a way that is *manifestly* true: that is, under normal
 * program execution, the comparison is a tautology.
 *
 * If the comparison fails, we can deduce the device is under attack, so an
 * illegal instruction will be executed. The manner in which the comparison is
 * done is carefully constructed in assembly to minimize the possibility of
 * adversarial faults. This macro also implicitly launders both arguments since
 * the compiler doesn't see the comparison and can't learn any new information
 * from it.
 *
 * There are six variants of this macro: one for each of the six comparison
 * operations.
 *
 * This macro is intended to be used along with `launder32()` to handle detected
 * faults when implementing redundant checks, i.e. in places where the compiler
 * could otherwise prove statically unreachable. For example:
 * ```
 * if (launder32(x) == 0) {
 *   HARDENED_CHECK_EQ(x, 0);
 * }
 * ```
 * See `launder32()` for more details.
 */
#define HARDENED_CHECK_EQ(a_, b_) HARDENED_CHECK_(HARDENED_CHECK_OP_EQ_, a_, b_)
#define HARDENED_CHECK_NE(a_, b_) HARDENED_CHECK_(HARDENED_CHECK_OP_NE_, a_, b_)
#define HARDENED_CHECK_LT(a_, b_) HARDENED_CHECK_(HARDENED_CHECK_OP_LT_, a_, b_)
#define HARDENED_CHECK_GT(a_, b_) HARDENED_CHECK_(HARDENED_CHECK_OP_GT_, a_, b_)
#define HARDENED_CHECK_LE(a_, b_) HARDENED_CHECK_(HARDENED_CHECK_OP_LE_, a_, b_)
#define HARDENED_CHECK_GE(a_, b_) HARDENED_CHECK_(HARDENED_CHECK_OP_GE_, a_, b_)

#ifdef __cplusplus
}
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
