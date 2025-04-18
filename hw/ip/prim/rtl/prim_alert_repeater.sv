// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Staged flop repeater to cut the crirtical path on alert signals when travelling
// in the larger SoC. Both TX and RX are staged with a single flop stage.

module prim_alert_repeater
  import prim_alert_pkg::*;
(
  input                             clk_i,
  input                             rst_ni,
  // Input interface
  input  prim_alert_pkg::alert_tx_t alert_tx_i
  output prim_alert_pkg::alert_rx_t alert_rx_o,
  // Flopped output interface
  output prim_alert_pkg::alert_tx_t alert_staged_tx_o,
  input  prim_alert_pkg::alert_rx_t alert_staged_rx_i
);
  prim_flop #(
    .ResetValue(0)
  ) u_tx_p (
    .clk_i,
    .rst_ni,
    .d_i    (alert_tx_i.alert_p),
    .q_o    (alert_staged_tx_o.alert_p)
  );

  prim_flop #(
    .ResetValue(1)
  ) u_tx_n (
    .clk_i,
    .rst_ni,
    .d_i    (alert_tx_i.alert_n),
    .q_o    (alert_staged_tx_o.alert_n)
  );

  prim_flop #(
    .ResetValue(0)
  ) u_rx_ping_p (
    .clk_i,
    .rst_ni,
    .d_i    (alert_staged_rx_i.ping_p),
    .q_o    (alert_rx_o.ping_p)
  );

  prim_flop #(
    .ResetValue(1)
  ) u_rx_ping_n (
    .clk_i,
    .rst_ni,
    .d_i    (alert_staged_rx_i.ping_n),
    .q_o    (alert_rx_o.ping_n)
  );

  prim_flop #(
    .ResetValue(0)
  ) u_rx_ack_p (
    .clk_i,
    .rst_ni,
    .d_i    (alert_staged_rx_i.ack_p),
    .q_o    (alert_rx_o.ack_p)
  );

  prim_flop #(
    .ResetValue(1)
  ) u_rx_ack_n (
    .clk_i,
    .rst_ni,
    .d_i    (alert_staged_rx_i.ack_n),
    .q_o    (alert_rx_o.ack_n)
  );
endmodule : prim_alert_repeater
