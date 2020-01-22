// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for prim_arbiter_ppc.
// Intended to be used with a formal tool.

module prim_arbiter_ppc_assert_fpv #(
  parameter int unsigned N = 4,
  parameter int unsigned DW = 32 
) (
  input  clk_i,
  input  rst_ni,
  input [N-1:0] req_i,
  input [DW-1:0]data_i [N],
  input logic[N-1:0] gnt_o,
  input logic[$clog2(N)-1:0] idx_o,
  input logic valid_o,
  input logic[DW-1:0] data_o,
  input  ready_i
);

  ///////////////////////////////
  // Declarations & Parameters //
  ///////////////////////////////

  /////////////////
  // Assumptions //
  /////////////////

  // `ASSUME(MyAssumption_M, ..., clk_i, !rst_ni)

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // `ASSERT(MyFwdAssertion_A, ..., clk_i, !rst_ni)

  /////////////////////////
  // Backward Assertions //
  /////////////////////////

  // `ASSERT(MyBkwdAssertion_A, ..., clk_i, !rst_ni)

endmodule : prim_arbiter_ppc_assert_fpv
