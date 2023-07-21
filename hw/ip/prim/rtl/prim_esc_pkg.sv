// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_esc_pkg;

  //////////////////////////////////////////////
  // Escalation monitor counter configuration //
  //////////////////////////////////////////////

  // This counter monitors incoming ping requests on the prim_esc_receiver side and auto-escalates
  // if the alert handler ceases to send them regularly. The maximum number of cycles between
  // subsequent ping requests is N_ESC_SEV x (2 x 2 x 2**PING_CNT_DW), see also implementation of
  // the ping timer (alert_handler_ping_timer.sv). The timeout counter below uses a timeout that
  // is 4x larger than that in order to incorporate some margin.

  parameter int MarginFactor = 4;
  parameter int NumWaitCounts = 2;
  parameter int NumTimeoutCounts = 2;
  // The number of escalation severities.
  // Leave this as-is unless the Alert Handler is reparameterized.
  parameter int NumEscSev = 4;
  // The width of the Alert Handler's ping counter.
  // Leave this as-is unless the Alert Handler is reparameterized.
  parameter int PingCntDw = 16;

  //////////////////////
  // Type definitions //
  //////////////////////

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
