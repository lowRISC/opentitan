// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_count.
// Intended to be used with a formal tool.

`include "prim_assert.sv"

module prim_count_tb #(
  parameter int Width = 2,
  parameter logic [Width-1:0] ResetValue = '0
) (
  input clk_i,
  input rst_ni,
  input clr_i,
  input set_i,
  input [Width-1:0] set_cnt_i,
  input incr_en_i,
  input decr_en_i,
  input [Width-1:0] step_i,
  output logic [Width-1:0] cnt_o,
  output logic [Width-1:0] cnt_next_o,
  output logic err_o
);

  prim_count #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_counter (
    .clk_i,
    .rst_ni,
    .clr_i,
    .set_i,
    .set_cnt_i,
    .incr_en_i,
    .decr_en_i,
    .step_i,
    .cnt_o,
    .cnt_next_o,
    .err_o
  );

endmodule : prim_count_tb
