// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_

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

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_H_
