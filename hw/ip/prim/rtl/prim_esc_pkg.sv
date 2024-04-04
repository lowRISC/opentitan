// Copyright lowRISC contributors (OpenTitan project).
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

  parameter esc_tx_t ESC_TX_DEFAULT = '{esc_p:  1'b0,
                                        esc_n:  1'b1};

  parameter esc_rx_t ESC_RX_DEFAULT = '{resp_p: 1'b0,
                                        resp_n: 1'b1};

endpackage : prim_esc_pkg
