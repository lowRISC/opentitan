// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_esc_pkg;
  typedef struct packed {
    logic esc_p;
    logic esc_n;
  } esc_tx_t;

  typedef struct packed {
    logic resp_p;
    logic resp_n;
  } esc_rx_t;
endpackage
