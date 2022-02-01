// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_max_tree.
// Intended to be used with a formal tool.

module prim_max_tree_tb #(
  parameter int NumSrc = 32,
  parameter int Width = 8,
  localparam int SrcWidth = $clog2(NumSrc)
) (
  input  clk_i,
  input  rst_ni,
  input [NumSrc-1:0][Width-1:0] values_i,
  input [NumSrc-1:0] valid_i,
  output logic[Width-1:0] max_value_o,
  output logic[SrcWidth-1:0] max_idx_o,
  output logic max_valid_o
);


  prim_max_tree #(
    .NumSrc(NumSrc),
    .Width(Width)
  ) dut (
    .clk_i,
    .rst_ni,
    .values_i,
    .valid_i,
    .max_value_o,
    .max_idx_o,
    .max_valid_o
  );


endmodule : prim_max_tree_tb
