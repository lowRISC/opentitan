// Copyright lowRISC contributors (OpenTitan project).
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
  kMultiBitBool4True = 0x6,
  kMultiBitBool4False = 0x9,

  /**
   * 8-bits boolean values
   */
  kMultiBitBool8True = 0x96,
  kMultiBitBool8False = 0x69,

  /**
   * 12-bits boolean values
   */
  kMultiBitBool12True = 0x696,
  kMultiBitBool12False = 0x969,

  /**
   * 16-bits boolean values
   */
  kMultiBitBool16True = 0x9696,
  kMultiBitBool16False = 0x6969,

  /**
   * 20-bits boolean values
   */
  kMultiBitBool20True = 0x69696,
  kMultiBitBool20False = 0x96969,

  /**
   * 24-bits boolean values
   */
  kMultiBitBool24True = 0x969696,
  kMultiBitBool24False = 0x696969,

  /**
   * 28-bits boolean values
   */
  kMultiBitBool28True = 0x6969696,
  kMultiBitBool28False = 0x9696969,

  /**
   * 32-bits boolean values
   */
  kMultiBitBool32True = 0x96969696,
  kMultiBitBool32False = 0x69696969,

} multi_bit_bool_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_H_
