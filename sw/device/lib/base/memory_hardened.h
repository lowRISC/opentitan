// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_HARDENED_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_HARDENED_H_

/**
 * @file
 * @brief OpenTitan Hardened Memory Function Library
 *
 * This library provides implementation of memory functions for copy, set
 * and mask memory regions which verifies completition of the operations.
 *
 * Fast shuffling of memory accesses is done by choosing:
 *  1. random stride for memory accesses
 *  2. random starting position
 *
 * Stride is selected to be co-prime with length, so we can simply add it
 * at each iteration and be sure we will go through all elements.
 * This also gives opportunity to add decoy memory accesses.
 *
 * Such implementation avoids computing random permutations and still
 * introduce enough noise, while being just 2x slower than regular memcpy().
 */

#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"

#ifdef __cplusplus
extern "C" {
// C++ don't have `restrict` keyword
#define restrict
#endif  // __cplusplus

/**
 * Fault resistant memcpy(). Checks that copy was fully done.
 *
 * @param dest Destination buffer
 * @param src Source buffer
 * @param len Bytes to copy
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t memcpy_checked(void *restrict dest, const void *restrict src,
                               size_t len);

/**
 * Memory copy with shuffled memory access pattern
 *
 * @param dest Destination buffer
 * @param src Source buffer
 * @param len Bytes to copy
 * @param seed Randomization seed for memory accesses order
 *
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t shuffled_memcpy(void *restrict dest, const void *restrict src,
                                size_t len, uint32_t seed);

/**
 * Memory copy with shuffled memory access pattern. Special version for case
 * where length is less or equal to 12 words (256/384 bits). Use other
 * than memcpy_shuffle approach and seed value identifies one of many orders
 * enumerated lexicographically.
 * Up to factorial(len_words) orders are possible.
 * This version can give more random orders than shuffled_memcpy() for small
 * data chunks.
 *
 * @param dest Destination buffer, 32-bit word aligned
 * @param src Source buffer, 32-bit word aligned
 * @param len_words 32-bit Words to copy, should be less or equal to 12
 * @param seed Seed to select particular permutation
 *
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t shuffled_memcpy32(uint32_t *restrict dest,
                                  const uint32_t *restrict src,
                                  size_t len_words, uint32_t seed);

/**
 * Calculate simple checksum of words with shuffled memory access.
 *
 * @param src1 First source array
 * @param src2 Second source array, optional (NULL), expected to be same size
 *             as src1 (typically a blinding mask)
 * @param len_words Length of src1 and src2 in 32-bit words
 * @param seed Randomization seed
 *
 * @return checksum
 */
uint32_t shuffled_checksum(const uint32_t *src1, const uint32_t *src2,
                           size_t len_words, uint32_t seed);

/**
 * Set memory to zero, fault resistant, checks for completion.
 *
 * @param dest Destination buffer
 * @param len Length in bytes
 *
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t memclear_checked(void *dest, size_t len);

/**
 * Fault resistant wiping of secrets checking that wipe was fully done.
 * It doesn't have to have cryptographic strength, so use something fast.
 * Useful for generation of blinding mask for use with memxor_checked().
 *
 * @param dest Destination buffer to wipe
 * @param len  Length in bytes
 *
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t wipe_checked(void *dest, size_t len, uint32_t seed);

/**
 * Memory xoring dest = src1 ^ src2. Useful for blinding / unbliding
 * secrets in memory.
 *
 * @param dest Destination buffer. Can alias src1 or src2.
 * @param src1 First source buffer
 * @param src2 Second source buffer
 * @param len Length of dest (and src1, src2) in bytes
 *
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t memxor_checked(void *dest, const void *restrict src1,
                               const void *restrict src2, size_t len);

/**
 * Reverse byte order of 32-bit word array in place.
 * Useful for conversion big numbers between little/big endian representation.
 *
 * @param dest Source/Destination array
 * @param len_words Size of dest in 32-bit words, up to 256
 * @param seed Randomization seed for memory access order
 *
 * @return `kHardenedBoolTrue` if everything is ok, undefined value else.
 *         The only guaranteed result is kHardenedBoolTrue.
 */
hardened_bool_t shuffled_reverse32(uint32_t *dest, size_t len_words,
                                   uint32_t seed);

/**
 * Constant time memcmp() with checked completion status.
 *
 * @param dest Destination buffer
 * @param src Dource buffer
 * @param len Bytes to compare
 *
 * @return `kHardenedBoolTrue` if memory location content is equal. Other values
 *         indicates either error or mismatch.
 */
hardened_bool_t memcmp_checked(const void *dest, const void *src, size_t len);

/**
 * Fault Resistant, constant time compare for equality with shuffled memory
 * access pattern. Mostly useful to deal with private keys.
 *
 * @param dest Destination buffer
 * @param src Dource buffer
 * @param len Bytes to compare
 * @param seed Randomization seed
 *
 * @return `kHardenedBoolTrue` if memory location's content is equal. Other
 *         values indicates either mismatch or attempts to inject faults.
 */
hardened_bool_t shuffled_memcmp(const void *dest, const void *src, size_t len,
                                uint32_t seed);

#ifdef __cplusplus
#undef restrict
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_HARDENED_H_
