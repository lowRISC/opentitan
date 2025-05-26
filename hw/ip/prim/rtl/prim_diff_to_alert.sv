// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim_diff_to_alert: This module receives a differentially encoded alert request and translates
// that to an alert signal with the alert protocol.

module prim_diff_to_alert #(
  // AsyncOn: Enables additional synchronization logic within the alert receiver.
  parameter bit AsyncOn = 1'b1,
  // Alert sender will latch the incoming alert event permanently and
  // keep on sending alert events until the next reset.
  parameter bit IsFatal = 1'b1
) (
  input logic                       clk_i,
  input logic                       rst_ni,
  // Input diff pair (differentially encoded alert signal)
  input logic                       diff_pi,
  input logic                       diff_ni,
  // Alert pair (interface signals for the alert protocol)
  input  prim_alert_pkg::alert_rx_t alert_rx_i,
  output prim_alert_pkg::alert_tx_t alert_tx_o
);
  logic diff_p_sync, diff_n_sync;

  if (AsyncOn) begin : gen_async
    prim_flop_2sync #(
      .Width(2),
      .ResetValue(2'b10)
    ) u_sync (
      .clk_i,
      .rst_ni,
      .d_i  ( {diff_ni, diff_pi}         ),
      .q_o  ( {diff_n_sync, diff_p_sync} )
    );
  end else begin : gen_sync
    assign diff_p_sync = diff_pi;
    assign diff_n_sync = diff_ni;
  end

  // This prevents further tool optimizations of the differential signal.
  logic diff_p_buf, diff_n_buf;
  prim_sec_anchor_buf #(
    .Width(2)
  ) u_prim_buf_ack (
    .in_i  ( {diff_n_sync, diff_p_sync}  ),
    .out_o ( {diff_n_buf, diff_p_buf}   )
  );

  // Treat any positive value on `diff_p_buf` and any negative value on `diff_n_buf` as alert.
  logic alert_req;
  assign alert_req = diff_p_buf | ~diff_n_buf;

  prim_alert_sender #(
    .AsyncOn(AsyncOn),
    .IsFatal(IsFatal)
  ) u_prim_alert_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i  ( 1'b0      ),
    .alert_req_i   ( alert_req ),
    .alert_ack_o   (),
    .alert_state_o (),
    .alert_rx_i,
    .alert_tx_o
  );
endmodule
