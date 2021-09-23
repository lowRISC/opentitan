// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_count.
// Intended to be used with a formal tool.

module prim_count_tb
  import prim_count_pkg::*; #(
  parameter int Width = 2,
  parameter bit OutSelDnCnt = 1, // 0 selects up count
  parameter prim_count_style_e CntStyle = CrossCnt
) (
  input  clk_i,
  input  rst_ni,
  input  clr_i,
  input  set_i,
  input [Width-1:0] set_cnt_i,
  input  en_i,
  input [Width-1:0] step_i,
  output logic[Width-1:0] cnt_o,
  output logic err_o
);

  prim_count #(
    .Width(Width),
    .OutSelDnCnt(OutSelDnCnt),
    .CntStyle(CntStyle)
  ) u_counter (
    .clk_i,
    .rst_ni,
    .clr_i,
    .set_i,
    .set_cnt_i,
    .en_i,
    .step_i,
    .cnt_o,
    .err_o
  );

endmodule : prim_count_tb
