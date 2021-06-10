// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for escalation sender/receiver pair. Intended to use with
// a formal tool.

module prim_esc_rxtx_fpv
  import prim_esc_pkg::*;
(
  input        clk_i,
  input        rst_ni,
  // for sigint error injection only
  input        resp_err_pi,
  input        resp_err_ni,
  input        esc_err_pi,
  input        esc_err_ni,
  // normal I/Os
  input        esc_req_i,
  input        ping_req_i,
  output logic ping_ok_o,
  output logic integ_fail_o,
  output logic esc_en_o
);

  esc_rx_t esc_rx_in, esc_rx_out;
  esc_tx_t esc_tx_in, esc_tx_out;

  assign esc_rx_in.resp_p = esc_rx_out.resp_p ^ resp_err_pi;
  assign esc_rx_in.resp_n = esc_rx_out.resp_n ^ resp_err_ni;
  assign esc_tx_in.esc_p  = esc_tx_out.esc_p  ^ esc_err_pi;
  assign esc_tx_in.esc_n  = esc_tx_out.esc_n  ^ esc_err_ni;

  prim_esc_sender u_prim_esc_sender (
    .clk_i        ,
    .rst_ni       ,
    .ping_req_i   ,
    .ping_ok_o    ,
    .integ_fail_o ,
    .esc_req_i    ,
    .esc_rx_i     ( esc_rx_in  ),
    .esc_tx_o     ( esc_tx_out )
  );

  prim_esc_receiver #(
    // This reduces the state space for this counter
    // from 2**24 to 2**6 to speed up convergence.
    .TimeoutCntDw(6)
  ) u_prim_esc_receiver (
    .clk_i    ,
    .rst_ni   ,
    .esc_en_o ,
    .esc_rx_o     ( esc_rx_out ),
    .esc_tx_i     ( esc_tx_in  )
  );

endmodule : prim_esc_rxtx_fpv
