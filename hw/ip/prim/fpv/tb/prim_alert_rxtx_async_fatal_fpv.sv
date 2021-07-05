// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for alert sender/receiver pair. Intended to use with
// a formal tool.

module prim_alert_rxtx_async_fatal_fpv
  import prim_alert_pkg::*;
(
  input        clk_i,
  input        rst_ni,
  // for sigint error and skew injection only
  input        ping_err_pi,
  input        ping_err_ni,
  input [1:0]  ping_skew_i,
  input        ack_err_pi,
  input        ack_err_ni,
  input [1:0]  ack_skew_i,
  input        alert_err_pi,
  input        alert_err_ni,
  input [1:0]  alert_skew_i,
  // normal I/Os
  input        alert_test_i,
  input        alert_req_i,
  input        ping_req_i,
  output logic alert_ack_o,
  output logic alert_state_o,
  output logic ping_ok_o,
  output logic integ_fail_o,
  output logic alert_o
);

  // asynchronous case
  localparam bit AsyncOn = 1'b1;
  localparam bit IsFatal = 1'b1;

  logic ping_pd;
  logic ping_nd;
  logic ack_pd;
  logic ack_nd;
  logic alert_pd;
  logic alert_nd;

  alert_rx_t alert_rx_out, alert_rx_in;
  alert_tx_t alert_tx_out, alert_tx_in;

  // for the purposes of FPV, we currently emulate the asynchronous transition
  // only in terms of the skew it may introduce (which is limited to +- 1 cycle)
  logic [1:0] ping_pq;
  logic [1:0] ping_nq;
  logic [1:0] ack_pq;
  logic [1:0] ack_nq;
  logic [1:0] alert_pq;
  logic [1:0] alert_nq;

  assign ping_pd = alert_rx_out.ping_p;
  assign ping_nd = alert_rx_out.ping_n;
  assign ack_pd  = alert_rx_out.ack_p;
  assign ack_nd  = alert_rx_out.ack_n;
  assign alert_rx_in.ping_p = ping_pq[ping_skew_i[0]] ^ ping_err_pi;
  assign alert_rx_in.ping_n = ping_nq[ping_skew_i[1]] ^ ping_err_ni;
  assign alert_rx_in.ack_p  = ack_pq[ack_skew_i[0]] ^ ack_err_pi;
  assign alert_rx_in.ack_n  = ack_nq[ack_skew_i[1]] ^ ack_err_ni;

  assign alert_pd = alert_tx_out.alert_p;
  assign alert_nd = alert_tx_out.alert_n;
  assign alert_tx_in.alert_p = alert_pq[alert_skew_i[0]] ^ alert_err_pi;
  assign alert_tx_in.alert_n = alert_nq[alert_skew_i[1]] ^ alert_err_ni;

  prim_alert_sender #(
    .AsyncOn ( AsyncOn ),
    .IsFatal ( IsFatal )
  ) i_prim_alert_sender (
    .clk_i      ,
    .rst_ni     ,
    .alert_test_i,
    .alert_req_i,
    .alert_ack_o,
    .alert_state_o,
    .alert_rx_i ( alert_rx_in  ),
    .alert_tx_o ( alert_tx_out )
  );

  prim_alert_receiver #(
    .AsyncOn ( AsyncOn )
  ) i_prim_alert_receiver (
    .clk_i        ,
    .rst_ni       ,
    .ping_req_i    ,
    .ping_ok_o    ,
    .integ_fail_o ,
    .alert_o      ,
    .alert_rx_o ( alert_rx_out ),
    .alert_tx_i ( alert_tx_in  )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_skew_delay
    if (!rst_ni) begin
      ping_pq  <= '0;
      ping_nq  <= '1;
      ack_pq   <= '0;
      ack_nq   <= '1;
      alert_pq <= '0;
      alert_nq <= '1;
    end else begin
      ping_pq  <= {ping_pq [$high(ping_pq )-1:0], ping_pd};
      ping_nq  <= {ping_nq [$high(ping_nq )-1:0], ping_nd};
      ack_pq   <= {ack_pq  [$high(ack_pq  )-1:0], ack_pd};
      ack_nq   <= {ack_nq  [$high(ack_nq  )-1:0], ack_nd};
      alert_pq <= {alert_pq[$high(alert_pq)-1:0], alert_pd};
      alert_nq <= {alert_nq[$high(alert_nq)-1:0], alert_nd};
    end
  end

endmodule : prim_alert_rxtx_async_fatal_fpv
