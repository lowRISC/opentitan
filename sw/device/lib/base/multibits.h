// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_H_

/**
 * Multi-bit boolean values
 *
 * Certain configuration fields in the design are multi-bits.
 * This gives the configuration fields redundancy and ensures
 * it is difficult to fault the values to a "good" state.
 */
typedef enum multi_bit_bool {

  /**
   * 4-bits boolean values
   */
  kMultiBitBool4True = 0xA,
  kMultiBitBool4False = 0x5,

  /**
   * 8-bits boolean values
   */
  kMultiBitBool8True = 0x5A,
  kMultiBitBool8False = 0xA5,

  /**
   * 12-bits boolean values
   */
  kMultiBitBool12True = 0xA5A,
  kMultiBitBool12False = 0x5A5,

  /**
   * 16-bits boolean values
   */
  kMultiBitBool16True = 0x5A5A,
  kMultiBitBool16False = 0xA5A5,

} multi_bit_bool_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_H_
