// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_arbiter_tree.
// Intended to be used with a formal tool.

module prim_arbiter_tree_fpv #(
  parameter int N = 8,
  parameter int DW = 32,
  parameter bit EnDataPort = 1,
  localparam int IdxW = $clog2(N)
) (
  input clk_i,
  input rst_ni,

  input                    req_chk_i,

  input        [ N-1:0]    req_i,
  input        [DW-1:0]    data_i [N],
  output logic [ N-1:0]    gnt_o,
  output logic [IdxW-1:0]  idx_o,

  output logic             valid_o,
  output logic [DW-1:0]    data_o,
  input                    ready_i
);


  prim_arbiter_tree #(
    .N(N),
    .DW(DW),
    .EnDataPort(EnDataPort)
  ) i_prim_arbiter_tree (
    .clk_i,
    .rst_ni,
    .req_chk_i,
    .req_i,
    .data_i,
    .gnt_o,
    .idx_o,
    .valid_o,
    .data_o,
    .ready_i
  );


endmodule : prim_arbiter_tree_fpv
