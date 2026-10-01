// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_flop #(
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    if (ResetValue[idx] == 1'b0) begin : g_reset_low
      // RESET_B is active-low async reset; ties to rst_ni so reset->Q=0.
      sg13cmos5l_dfrbp_1 u_flop (
        .CLK    (clk_i),
        .D      (d_i[idx]),
        .RESET_B(rst_ni),
        .Q      (q_o[idx]),
        .Q_N    ()
      );
    end else begin : g_reset_high
      // Invert D going in, take Q_N out. So, double inversion cancels in normal
      // operation. On reset (RESET_B low), Q->0 so Q_N->1, giving reset-to-1.
      logic d_n;
      sg13cmos5l_inv_1 u_inv (
        .A(d_i[idx]),
        .Y(d_n)
      );
      sg13cmos5l_dfrbp_1 u_flop (
        .CLK    (clk_i),
        .D      (d_n),
        .RESET_B(rst_ni),
        .Q      (),
        .Q_N    (q_o[idx])
      );
    end
  end

endmodule
