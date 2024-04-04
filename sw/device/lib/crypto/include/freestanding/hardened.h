// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_FREESTANDING_HARDENED_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_FREESTANDING_HARDENED_H_

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
  kHardenedBoolTrue = 0x739,
  /**
   * The falsey value, expected to be used like #false.
   */
  kHardenedBoolFalse = 0x1d4,
} hardened_bool_t;

#ifdef __cplusplus
}
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_FREESTANDING_HARDENED_H_
