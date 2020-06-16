// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_arbiter_ppc.
// Intended to be used with a formal tool.

module prim_arbiter_ppc_fpv #(
  parameter int unsigned N = 8,
  parameter int unsigned DW = 32,
  parameter bit EnDataPort = 1,
  parameter bit EnReqStabA = 1,
  localparam int IdxW = $clog2(N)
) (
  input clk_i,
  input rst_ni,

  input        [ N-1:0]    req_i,
  input        [DW-1:0]    data_i [N],
  output logic [ N-1:0]    gnt_o,
  output logic [IdxW-1:0]  idx_o,

  output logic             valid_o,
  output logic [DW-1:0]    data_o,
  input                    ready_i
);


  prim_arbiter_ppc #(
    .N(N),
    .DW(DW),
    .EnDataPort(EnDataPort),
    .EnReqStabA(EnReqStabA)
  ) i_prim_arbiter_ppc (
    .clk_i,
    .rst_ni,
    .req_i,
    .data_i,
    .gnt_o,
    .idx_o,
    .valid_o,
    .data_o,
    .ready_i
  );


endmodule : prim_arbiter_ppc_fpv
