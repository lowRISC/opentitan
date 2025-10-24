// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_flop_no_rst #(
  parameter int Width = 1
) (
  input  logic             clk_i,
  input  logic [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic [Width-1:0] qn;

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    DFFHQNx1_ASAP7_75t_R u_size_only_flop (
      .CLK(clk_i),
      .D  (d_i[idx]),
      .QN (qn[idx])
    );
    assign q_o[idx] = ~qn[idx];
  end

endmodule
