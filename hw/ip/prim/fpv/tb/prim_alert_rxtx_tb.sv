// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for alert sender/receiver pair. Intended to use with
// a formal tool.

module prim_alert_rxtx_tb (
  input        clk_i,
  input        rst_ni,
  // for sigint error injection only
  input        ping_err_pi,
  input        ping_err_ni,
  input        ack_err_pi,
  input        ack_err_ni,
  input        alert_err_pi,
  input        alert_err_ni,
  // normal I/Os
  input        alert_i,
  input        ping_en_i,
  output logic ping_ok_o,
  output logic integ_fail_o,
  output logic alert_o
);

  // synchronous case
  localparam bit AsyncOn = 1'b0;

  logic ping_p;
  logic ping_n;
  logic ack_p;
  logic ack_n;
  logic alert_p;
  logic alert_n;

  prim_alert_sender #(
    .AsyncOn ( AsyncOn )
  ) i_prim_alert_sender (
    .clk_i    ,
    .rst_ni   ,
    .alert_i  ,
    .ping_pi  ( ping_p ^ ping_err_pi ),
    .ping_ni  ( ping_n ^ ping_err_ni ),
    .ack_pi   ( ack_p  ^ ack_err_pi  ),
    .ack_ni   ( ack_n  ^ ack_err_ni  ),
    .alert_po ( alert_p  ),
    .alert_no ( alert_n  )
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
    .ping_po      ( ping_p       ),
    .ping_no      ( ping_n       ),
    .ack_po       ( ack_p        ),
    .ack_no       ( ack_n        ),
    .alert_pi     ( alert_p ^ alert_err_pi ),
    .alert_ni     ( alert_n ^ alert_err_ni )
  );

endmodule : prim_alert_rxtx_tb
