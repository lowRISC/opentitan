// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// One-hot mux
// A AND/OR mux with a one-hot select input.

`include "prim_assert.sv"

module prim_onehot_mux #(
  parameter int Width  = 32,
  parameter int Inputs = 8
) (
  // Clock and reset only for assertions
  input clk_i,
  input rst_ni,

  input  logic [Width-1:0]  in_i [Inputs],
  input  logic [Inputs-1:0] sel_i, // Must be one-hot or zero
  output logic [Width-1:0]  out_o
);
  logic [Inputs-1:0] in_mux [Width];

  for (genvar b = 0; b < Width; ++b) begin : g_in_mux_outer
    logic [Inputs-1:0] out_mux_bits;

    for (genvar i = 0; i < Inputs; ++i) begin : g_in_mux_inner
      assign in_mux[b][i] = in_i[i][b];
    end

    prim_and2 #(.Width(Inputs)) u_mux_bit_and(
      .in0_i(in_mux[b]),
      .in1_i(sel_i),
      .out_o(out_mux_bits)
    );

    assign out_o[b] = |out_mux_bits;
  end

  logic unused_clk;
  logic unused_rst_n;

  // clock and reset only needed for assertion
  assign unused_clk   = clk_i;
  assign unused_rst_n = rst_ni;

  `ASSERT(SelIsOnehot_A, $onehot0(sel_i))
endmodule
