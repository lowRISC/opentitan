// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_MEMORY_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_MEMORY_H_

/**
 * @file
 * @brief Hardened memory operations for constant power buffer manipulation.
 */

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Expects some external implementation of randomness to be linked.
 *
 * @return A fresh random word.
 */
extern uint32_t hardened_memshred_random_word(void);

/**
 * Copies 32-bit words between non-overlapping regions.
 *
 * Unlike `memcpy()`, this function has important differences:
 * - It is significantly slower, since it mitigates power-analysis attacks.
 * - It performs operations on 32-bit words, rather than bytes.
 * - It returns a status.
 *
 * Input pointers *MUST* be 32-bit aligned, although they do not need to
 * actually point to memory declared as `uint32_t` per the C aliasing rules.
 * Internally, this function is careful to not dereference its operands
 * directly, and instead uses dedicated load/store intrinsics.
 *
 * @param dest The destination of the copy.
 * @param src The source of the copy.
 * @param word_len The number of words to copy.
 * @return OK or error.
 */
status_t hardened_memcpy(uint32_t *OT_RESTRICT dest,
                         const uint32_t *OT_RESTRICT src, size_t word_len);

/**
 * Fills a 32-bit aligned region of memory with random data.
 *
 * Unlike `memset()`, this function has important differences:
 * - It is significantly slower, since it mitigates power-analysis attacks.
 * - It performs operations on 32-bit words, rather than bytes.
 * - A fill value cannot be specified.
 * - It returns a status.
 *
 * Input pointers *MUST* be 32-bit aligned, although they do not need to
 * actually point to memory declared as `uint32_t` per the C aliasing rules.
 * Internally, this function is careful to not dereference its operands
 * directly, and instead uses dedicated load/store intrinsics.
 *
 * @param dest The destination of the set.
 * @param word_len The number of words to write.
 * @return OK or error.
 */
status_t hardened_memshred(uint32_t *dest, size_t word_len);

/**
 * Compare two potentially-overlapping 32-bit aligned regions of memory for
 * equality.
 *
 * Unlike `memcmp()`, this function has important differences:
 * - It is significantly slower, since it mitigates power-analysis attacks.
 * - It performs operations on 32-bit words, rather than bytes.
 * - It only computes equality, not lexicographic ordering, which would be even
 *   slower.
 * - It returns a `hardened_bool_t`.
 * - It is constant-time.
 *
 * Input pointers *MUST* be 32-bit aligned, although they do not need to
 * actually point to memory declared as `uint32_t` per the C aliasing rules.
 * Internally, this function is careful to not dereference its operands
 * directly, and instead uses dedicated load/store intrinsics.
 *
 * @param lhs The first buffer to compare.
 * @param rhs The second buffer to compare.
 * @param word_len The number of words to compare.
 */
hardened_bool_t hardened_memeq(const uint32_t *lhs, const uint32_t *rhs,
                               size_t word_len);

/**
 * Constant time memeq implementation that can also handle non 32-bit aligned
 * buffers.
 *
 * SCA protection is provided by choosing a random start index for the
 * comparison.
 *
 * CAUTION! This function is not considered as secure as `hardened_memeq` due to
 * the byte-sized memory accesses vs. 32b word accesses.
 *
 * @param lhs The first buffer to compare.
 * @param rhs The second buffer to compare.
 * @param word_len The number of bytes to compare.
 */
hardened_bool_t consttime_memeq_byte(const void *lhs, const void *rhs,
                                     size_t len);

/**
 * Combines two word buffers with XOR and store the result in the dest. buffer.
 *
 * Performs dest = ((rand ^ x) ^ y) ^ rand
 *
 * Callers should ensure the entropy complex is up before calling this
 * function. The implementation uses random-order hardening primitives for
 * side-channel defense. Moreover, calles should ensure that the dest. buffer
 * is different from the source buffers.
 *
 * @param x Pointer to the first operand.
 * @param y Pointer to the second operand.
 * @param word_len Length in words of each operand.
 * @param dest[out] Pointer to the output buffer.
 * @return OK or error.
 */
status_t hardened_xor(const uint32_t *OT_RESTRICT x,
                      const uint32_t *OT_RESTRICT y, size_t word_len,
                      uint32_t *OT_RESTRICT dest);

/**
 * Combines two word buffers with XOR in-place.
 *
 * Callers should ensure the entropy complex is up before calling this
 * function. The implementation uses random-order hardening primitives for
 * side-channel defense.
 *
 * @param[in,out] x Pointer to the first operand (modified in-place).
 * @param y Pointer to the second operand.
 * @param word_len Length in words of each operand.
 * @return OK or error.
 */
status_t hardened_xor_in_place(uint32_t *OT_RESTRICT x,
                               const uint32_t *OT_RESTRICT y, size_t word_len);

/**
 * Copy memory between non-overlapping regions with a randomized byte traversal.
 *
 * CAUTION! This function is not considered as secure as `hardened_memcpy` due
 * to the byte-sized memory accesses vs. 32b word accesses. After this function,
 * a `consttime_memeq_byte(src, dest, byte_len)` should follow to check if the
 * bytecopy was successful (see lowRISC/opentitan#8815). Switch the function
 * arguments as shown in the example to also cover faults directly on the
 * pointers.
 *
 * @param dest the region to copy to.
 * @param src the region to copy from.
 * @param byte_len, the number of bytes to copy.
 * @return Result of the operation (OK or error).
 */
status_t randomized_bytecopy(void *OT_RESTRICT dest,
                             const void *OT_RESTRICT src, size_t byte_len);

/**
 * In-place XOR of two non-overlapping memory regions with a randomized byte
 * traversal.
 *
 * CAUTION! This function is not considered as secure as `hardened_xor_in_place`
 * due to the byte-sized memory accesses vs. 32b word accesses.
 *
 * @param x Pointer to the first operand (modified in-place).
 * @param y Pointer to the second operand.
 * @param byte_len, the number of bytes to XOR.
 * @return Result of the operation (OK or error).
 */
status_t randomized_bytexor_in_place(void *OT_RESTRICT x,
                                     const void *OT_RESTRICT y,
                                     size_t byte_len);

/**
 * Combines two word buffers with ADD and store the result in the dest. buffer.
 *
 * Warning: Only limited SCA hardening measures are applied due to the nature of
 * arithmetic operations. guaranteed. The function is hardened against fault
 * injections.
 *
 * This mimics the OTBN `add`.
 *
 * @param x Pointer to the first operand.
 * @param y Pointer to the second operand.
 * @param word_len Length in words of each operand.
 * @param dest[out] Pointer to the output buffer.
 * @return OK or error.
 */
status_t hardened_add(const uint32_t *OT_RESTRICT x,
                      const uint32_t *OT_RESTRICT y, size_t word_len,
                      uint32_t *OT_RESTRICT dest);

/**
 * Combines two word buffers with SUB and store the result in the dest. buffer.
 *
 * Warning: the side-channel protection of this function call can not be
 * guaranteed.
 * The function is hardened against fault injections.
 *
 * This mimics the OTBN `sub`.
 *
 * @param x Pointer to the first operand.
 * @param y Pointer to the second operand.
 * @param word_len Length in words of each operand.
 * @param dest[out] Pointer to the output buffer.
 * @return OK or error.
 */
status_t hardened_sub(const uint32_t *OT_RESTRICT x,
                      const uint32_t *OT_RESTRICT y, size_t word_len,
                      uint32_t *OT_RESTRICT dest);

/**
 * Perform a modular subtraction of two multi-word values.
 *
 * It computes (x - y) mod n. The values are expected to follow a
 * little-endian layout.
 *
 * Warning: the side-channel protection of this function call can not be
 * guaranteed. The function is hardened against fault injections and is
 * constant time in the value being reduced.
 *
 * In order to have this function constant time, it conditionally adds n only
 * once.
 * This function mimics OTBN's subm.
 *
 * @param x Pointer to the first operand.
 * @param y Pointer to the second operand.
 * @param n Pointer to the multi-word modulus.
 * @param word_len Length in words of each operand and the modulus.
 * @param[out] dest Pointer to the multi-word result.
 * @return OK or error.
 */
status_t hardened_sub_mod(const uint32_t *OT_RESTRICT x,
                          const uint32_t *OT_RESTRICT y,
                          const uint32_t *OT_RESTRICT n, size_t word_len,
                          uint32_t *OT_RESTRICT dest);

/**
 * Perform a modular addition of two multi-word values.
 *
 * It computes (x + y) mod n. The values are expected to follow a
 * little-endian layout.
 *
 * Warning: the side-channel protection of this function call can not be
 * guaranteed. The function is hardened against fault injections and is
 * constant time in the value being reduced.
 *
 * In order to have this function constant time, it conditionally subtracts n
 * only once.
 * This function mimics OTBN's addm.
 *
 * @param x Pointer to the first operand.
 * @param y Pointer to the second operand.
 * @param n Pointer to the multi-word modulus.
 * @param word_len Length in words of each operand and the modulus.
 * @param[out] dest Pointer to the multi-word result.
 * @return OK or error.
 */
status_t hardened_add_mod(const uint32_t *OT_RESTRICT x,
                          const uint32_t *OT_RESTRICT y,
                          const uint32_t *OT_RESTRICT n, size_t word_len,
                          uint32_t *OT_RESTRICT dest);

/**
 * Perform a range check whether the value is larger than zero and smaller than
 * N. Namely, it checks whether 0 < value < N. Values are expected to follow
 * little-endian layout.
 *
 * Warning: the side-channel protection of this function call can not be
 * guaranteed.
 * The function is hardened against fault injections and is constant time.
 *
 * @param value Pointer to the value to check.
 * @param N Pointer to the upper limit of the range.
 * @param word_len Length in words of value and N.
 * @return OK or error.
 */
status_t hardened_range_check(const uint32_t *value, const uint32_t *N,
                              size_t word_len);

/**
 * Perform a modular reduction of a multi-word value by a multi-word modulus.
 *
 * It checks whether value % n. The value is expected to follow a
 * little-endian layout.
 *
 * Warning: the side-channel protection of this function call can not be
 * guaranteed. The function is hardened against fault injections and is
 * constant time in the value being reduced.
 *
 * @param value Pointer to the value to check.
 * @param n Pointer to the multi-word modulus.
 * @param word_len Length in words of value.
 * @param[out] result Pointer to the multi-word result.
 * @return OK or error.
 */
status_t hardened_mod_reduce(const uint32_t *value, const uint32_t *n,
                             size_t word_len, uint32_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_MEMORY_H_
