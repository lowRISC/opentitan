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

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    // IHP130 has no reset-free DFF; use a tiehi cell to drive RESET_B high.
    logic reset_b_tie;
    sg13cmos5l_tiehi u_tie (
      .L_HI(reset_b_tie)
    );
    sg13cmos5l_dfrbp_1 u_flop (
      .CLK    (clk_i),
      .D      (d_i[idx]),
      .RESET_B(reset_b_tie),
      .Q      (q_o[idx]),
      .Q_N    ()
    );
  end

endmodule
