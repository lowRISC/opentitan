// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The logic assumes that en_i is synchronized (so the instantiation site might need to put a
// synchronizer before en_i).

module prim_clock_gating #(
  parameter bit NoFpgaGate = 1'b0, // this parameter has no function in generic
  parameter bit FpgaBufGlobal = 1'b1 // this parameter has no function in generic
) (
  input  logic clk_i,
  input  logic en_i,
  input  logic test_en_i,
  output logic clk_o
);

  sg13cmos5l_slgcp_1 u_clock_gate (
    .GATE(en_i),
    .SCE (test_en_i),
    .CLK (clk_i),
    .GCLK(clk_o)
  );

endmodule
