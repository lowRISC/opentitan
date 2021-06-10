// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_

#include <stdint.h>
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
 * Hardened select of word without branches.
 *
 * @param test the value to test
 * @param a the value returned if 'test' is not 0
 * @param b the value returned if 'test' is zero
 *
 * @return a if test==0 and b otherwise;
 *
 * This function is mostly useful when test == 0 is a good result and
 * hardening is required to prevent easy generation of 'b'.
 *
 * Example:
 *   hardened_select_if_zero(test, kHardenedBoolFalse, kHardenedBoolTrue)
 *
 * We need a form where skipping instruction will not allow to
 * produce kHardenedBoolTrue, on RV32 try to get 'snez' instead of 'seqz'
 * as snez will transform non-zero reg into non-zero, so skipping it
 * won't cause an inversion of value.
 * Constant 7 is choosen to prevent input values in 0xfffffff0 - 0xffffffff
 * range to be converted to proper constant by skipping snez & neg.
 */
static inline uintptr_t hardened_select_if_zero(uintptr_t test, uintptr_t a,
                                                uintptr_t b) {
  uintptr_t mask = -((uintptr_t)(test * 7 != 0));
  return (mask & a) | (~mask & b);
}

/**
 * Branchless (bit) ? t : f for bit 0 or 1
 */
static inline void *hardened_select_if_bit_zero(uintptr_t bit, uintptr_t a,
                                                uintptr_t b) {
  bit -= 1; /* 0 -> 0xFFFFFFFF, 1 -> 0 */
  return (void *)((bit & (uintptr_t)b) | ((~bit) & (uintptr_t)a));
}

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
