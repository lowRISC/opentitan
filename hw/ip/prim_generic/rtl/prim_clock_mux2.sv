// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_clock_mux2 #(
  parameter bit NoFpgaBufG = 1'b0 // this parameter serves no function in the generic model
) (
  input        clk0_i,
  input        clk1_i,
  input        sel_i,
  output logic clk_o
);

  // We model the mux with logic operations for GTECH runs.
  assign clk_o = (sel_i & clk1_i) | (~sel_i & clk0_i);

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
