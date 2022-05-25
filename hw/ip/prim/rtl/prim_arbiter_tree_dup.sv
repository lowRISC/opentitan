// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is a wrapper module that instantiates two prim_aribter_tree modules.
// The reason for two is similar to modules such as prim_count/prim_lfsr where
// we use spatial redundancy to ensure the arbitration results are not altered.
//
// Note there are limits to this check, as the inputs to the duplicated arbiter
// is still a single lane. So an upstream attack can defeat this module.  The
// duplication merely protects against attacks directly on the arbiter.

`include "prim_assert.sv"

module prim_arbiter_tree_dup #(
  parameter int N   = 8,
  parameter int DW  = 32,

  // Configurations
  // EnDataPort: {0, 1}, if 0, input data will be ignored
  parameter bit EnDataPort = 1,

  // if arbiter has fixed priority
  parameter bit FixedArb = 0,

  // Derived parameters
  localparam int IdxW = $clog2(N)
) (
  input clk_i,
  input rst_ni,

  input                    req_chk_i, // Used for gating assertions. Drive to 1 during normal
                                      // operation.
  input        [ N-1:0]    req_i,
  input        [DW-1:0]    data_i [N],
  output logic [ N-1:0]    gnt_o,
  output logic [IdxW-1:0]  idx_o,

  output logic             valid_o,
  output logic [DW-1:0]    data_o,
  input                    ready_i,
  output logic             err_o
);

  localparam int ArbInstances = 2;

  //typedef struct packed {
  //  logic [N-1:0] req;
  //  logic [N-1:0][DW-1:0] data;
  //} arb_inputs_t;

  typedef struct packed {
    logic valid;
    logic [N-1:0] gnt;
    logic [IdxW-1:0] idx;
    logic [DW-1:0] data;
  } arb_outputs_t;

  // buffer up the inputs separately for each instance
  //arb_inputs_t arb_in;
  //arb_inputs_t [ArbInstances-1:0] arb_input_buf;
  arb_outputs_t [ArbInstances-1:0] arb_output_buf;

  for (genvar i = 0; i < ArbInstances; i++) begin : gen_input_bufs
    logic [N-1:0] req_buf;
    prim_buf #(
      .Width(N)
    ) u_req_buf (
      .in_i(req_i),
      .out_o(req_buf)
    );

    logic [DW-1:0] data_buf [N];
    for (genvar j = 0; j < N; j++) begin : gen_data_bufs
      prim_buf #(
        .Width(DW)
      ) u_dat_buf (
        .in_i(data_i[j]),
        .out_o(data_buf[j])
      );
    end

    if (FixedArb) begin : gen_fixed_arbiter
      prim_arbiter_fixed  #(
        .N(N),
        .DW(DW),
        .EnDataPort(EnDataPort)
      ) u_arb (
        .clk_i,
        .rst_ni,
        .req_i(req_buf),
        .data_i(data_buf),
        .gnt_o(arb_output_buf[i].gnt),
        .idx_o(arb_output_buf[i].idx),
        .valid_o(arb_output_buf[i].valid),
        .data_o(arb_output_buf[i].data),
        .ready_i
      );
      logic unused_req_chk;
      assign unused_req_chk = req_chk_i;

    end else begin : gen_rr_arbiter
      prim_arbiter_tree #(
        .N(N),
        .DW(DW),
        .EnDataPort(EnDataPort)
      ) u_arb (
        .clk_i,
        .rst_ni,
        .req_chk_i,
        .req_i(req_buf),
        .data_i(data_buf),
        .gnt_o(arb_output_buf[i].gnt),
        .idx_o(arb_output_buf[i].idx),
        .valid_o(arb_output_buf[i].valid),
        .data_o(arb_output_buf[i].data),
        .ready_i
      );
    end
  end

  // the last buffered position is sent out
  assign gnt_o = arb_output_buf[ArbInstances-1].gnt;
  assign idx_o = arb_output_buf[ArbInstances-1].idx;
  assign valid_o = arb_output_buf[ArbInstances-1].valid;
  assign data_o = arb_output_buf[ArbInstances-1].data;

  // Check the last buffer index against all other instances
  logic [ArbInstances-2:0] output_delta;

  for (genvar i = 0; i < ArbInstances-1; i++) begin : gen_checks
    assign output_delta[i] = arb_output_buf[ArbInstances-1] != arb_output_buf[i];
  end

  logic err_d, err_q;
  // There is an error if anything ever disagrees
  assign err_d = |output_delta;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_q <= '0;
    end else begin
      err_q <= err_d | err_q;
    end
  end

  assign err_o = err_q;

endmodule // prim_arbiter_tree
