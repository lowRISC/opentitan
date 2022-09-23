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
<%
from mubi import prim_mubi
%>\

% for n in range(1, n_max_nibbles + 1):
<%
   nbits = n * 4
%>\
  /**
   * ${nbits}-bits boolean values
   */
  kMultiBitBool${nbits}True = 0x${prim_mubi.mubi_value_as_hexstr(True, nbits)},
  kMultiBitBool${nbits}False = 0x${prim_mubi.mubi_value_as_hexstr(False, nbits)},

% endfor
} multi_bit_bool_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_H_
