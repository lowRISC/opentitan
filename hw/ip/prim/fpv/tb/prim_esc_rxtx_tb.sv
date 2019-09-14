// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for escalation sender/receiver pair. Intended to use with
// a formal tool.

module prim_esc_rxtx_tb (
  input        clk_i,
  input        rst_ni,
  // for sigint error injection only
  input        resp_err_pi,
  input        resp_err_ni,
  input        esc_err_pi,
  input        esc_err_ni,
  // normal I/Os
  input        esc_en_i,
  input        ping_en_i,
  output logic ping_ok_o,
  output logic integ_fail_o,
  output logic esc_en_o
);

  logic resp_p;
  logic resp_n;
  logic esc_p;
  logic esc_n;

  prim_esc_sender i_prim_esc_sender (
    .clk_i        ,
    .rst_ni       ,
    .ping_en_i    ,
    .ping_ok_o    ,
    .integ_fail_o ,
    .esc_en_i     ,
    .resp_pi      ( resp_p ^ resp_err_pi ),
    .resp_ni      ( resp_n ^ resp_err_ni ),
    .esc_po       ( esc_p                ),
    .esc_no       ( esc_n                )
  );

  prim_esc_receiver i_prim_esc_receiver (
    .clk_i    ,
    .rst_ni   ,
    .esc_en_o ,
    .resp_po  ( resp_p          ),
    .resp_no  ( resp_n          ),
    .esc_pi   ( esc_p  ^ esc_err_pi ),
    .esc_ni   ( esc_n  ^ esc_err_ni )
  );

endmodule : prim_esc_rxtx_tb
