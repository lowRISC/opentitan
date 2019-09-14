// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for alert sender/receiver pair. Intended to use with
// a formal tool.

module prim_alert_rxtx_async_tb (
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
  input        alert_i,
  input        ping_en_i,
  output logic ping_ok_o,
  output logic integ_fail_o,
  output logic alert_o
);

  // asynchronous case
  localparam bit AsyncOn = 1'b1;

  logic ping_pd;
  logic ping_nd;
  logic ack_pd;
  logic ack_nd;
  logic alert_pd;
  logic alert_nd;
  logic [1:0] ping_pq;
  logic [1:0] ping_nq;
  logic [1:0] ack_pq;
  logic [1:0] ack_nq;
  logic [1:0] alert_pq;
  logic [1:0] alert_nq;

  // for the purposes of FPV, we currently emulate the asynchronous transition
  // only in terms of the skew it may introduce (which is limited to +- 1 cycle)

  prim_alert_sender #(
    .AsyncOn ( AsyncOn )
  ) i_prim_alert_sender (
    .clk_i    ,
    .rst_ni   ,
    .alert_i  ,
    .ping_pi  ( ping_pq[ping_skew_i[0]] ^ ping_err_pi ),
    .ping_ni  ( ping_nq[ping_skew_i[1]] ^ ping_err_ni ),
    .ack_pi   ( ack_pq[ack_skew_i[0]]  ^ ack_err_pi  ),
    .ack_ni   ( ack_nq[ack_skew_i[1]]  ^ ack_err_ni  ),
    .alert_po ( alert_pd  ),
    .alert_no ( alert_nd  )
  );

  prim_alert_receiver #(
    .AsyncOn ( AsyncOn )
  ) i_prim_alert_receiver (
    .clk_i        ,
    .rst_ni       ,
    .ping_en_i    ,
    .ping_ok_o    ,
    .integ_fail_o ,
    .alert_o      ,
    .ping_po      ( ping_pd       ),
    .ping_no      ( ping_nd       ),
    .ack_po       ( ack_pd        ),
    .ack_no       ( ack_nd        ),
    .alert_pi     ( alert_pq[alert_skew_i[0]] ^ alert_err_pi ),
    .alert_ni     ( alert_nq[alert_skew_i[1]] ^ alert_err_ni )
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

endmodule : prim_alert_rxtx_async_tb
