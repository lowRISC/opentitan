// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Constants for use in primitives

package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ImplGeneric = 0,
    ImplXilinx  = 1
  } impl_e;

  // interface structs for prim_alert_* and prim_esc_*
  typedef struct packed {
    logic alert_p;
    logic alert_n;
  } alert_tx_t;

  typedef struct packed {
    logic ping_p;
    logic ping_n;
    logic ack_p;
    logic ack_n;
  } alert_rx_t;

  typedef struct packed {
    logic esc_p;
    logic esc_n;
  } esc_tx_t;

  typedef struct packed {
    logic resp_p;
    logic resp_n;
  } esc_rx_t;

endpackage : prim_pkg
