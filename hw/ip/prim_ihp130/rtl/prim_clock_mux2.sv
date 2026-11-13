// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_clock_mux2 #(
  parameter bit NoFpgaBufG = 1'b0 // this parameter serves no function in the generic model
) (
  input  logic clk0_i,
  input  logic clk1_i,
  input  logic sel_i,
  output logic clk_o
);

  sg13cmos5l_mux2_1 u_clock_mux (
    .A0(clk0_i),
    .A1(clk1_i),
    .S (sel_i),
    .X (clk_o)
  );

  // Make sure sel is never X.
  //
  // So that this can be a clocked assertion, we check it on the posedge of each input clock.
  //
  // This is disabled for FPV runs (because some formal tools don't have a concept of "X"). The
  // assertion comes after a ##1 to allow inverted clocks that start with a rising edge at the
  // beginning of the simulation.
`ifndef FPV_ON
  `ASSERT(selKnown0, ##1 !$isunknown(sel_i), clk0_i, 0)
  `ASSERT(selKnown1, ##1 !$isunknown(sel_i), clk1_i, 0)
`endif

endmodule : prim_clock_mux2
