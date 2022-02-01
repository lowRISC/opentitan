// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for prim_max_tree.
// Intended to be used with a formal tool.

`include "prim_assert.sv"

module prim_max_tree_assert_fpv #(
  parameter int NumSrc = 32,
  parameter int Width = 8,
  localparam int SrcWidth = $clog2(NumSrc)
) (
  input  clk_i,
  input  rst_ni,
  input [NumSrc-1:0][Width-1:0] values_i,
  input [NumSrc-1:0] valid_i,
  input logic[Width-1:0] max_value_o,
  input logic[SrcWidth-1:0] max_idx_o,
  input logic max_valid_o
);

  ///////////////////////////////
  // Declarations & Parameters //
  ///////////////////////////////

  /////////////////
  // Assumptions //
  /////////////////

  // `ASSUME(MyAssumption_M, ...)

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // `ASSERT(MyFwdAssertion_A, ...)

  /////////////////////////
  // Backward Assertions //
  /////////////////////////

  // `ASSERT(MyBkwdAssertion_A, ...)

endmodule : prim_max_tree_assert_fpv
