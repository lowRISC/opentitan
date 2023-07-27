// Copyright lowRISC contributors.
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

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Copies 32-bit words between non-overlapping regions.
 *
 * Unlike `memcpy()`, this function has important differences:
 * - It is significantly slower, since it mitigates power-analysis attacks.
 * - It performs operations on 32-bit words, rather than bytes.
 * - It returns void.
 *
 * Input pointers *MUST* be 32-bit aligned, although they do not need to
 * actually point to memory declared as `uint32_t` per the C aliasing rules.
 * Internally, this function is careful to not dereference its operands
 * directly, and instead uses dedicated load/store intrinsics.
 *
 * @param dest The destination of the copy.
 * @param src The source of the copy.
 * @param word_len The number of words to copy.
 */
void hardened_memcpy(uint32_t *OT_RESTRICT dest,
                     const uint32_t *OT_RESTRICT src, size_t word_len);

/**
 * Fills a 32-bit aligned region of memory with random data.
 *
 * Unlike `memset()`, this function has important differences:
 * - It is significantly slower, since it mitigates power-analysis attacks.
 * - It performs operations on 32-bit words, rather than bytes.
 * - A fill value cannot be specified.
 * - It returns void.
 *
 * Input pointers *MUST* be 32-bit aligned, although they do not need to
 * actually point to memory declared as `uint32_t` per the C aliasing rules.
 * Internally, this function is careful to not dereference its operands
 * directly, and instead uses dedicated load/store intrinsics.
 *
 * @param dest The destination of the set.
 * @param word_len The number of words to write.
 */
void hardened_memshred(uint32_t *dest, size_t word_len);

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
 * @param word_len The number of words to write.
 */
hardened_bool_t hardened_memeq(const uint32_t *lhs, const uint32_t *rhs,
                               size_t word_len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_MEMORY_H_
