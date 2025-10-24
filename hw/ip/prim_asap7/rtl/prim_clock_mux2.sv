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

  // there is no specific mux cell available in this technology. An AO cell with the
  // functionality Y=(A1&A2)|(B1&B2) is used instead. This is not ideal and a limitation
  // of this technology
  AO22x1_ASAP7_75t_R u_size_only_ao22 (
    .A1(clk0_i),
    .A2(~sel_i),
    .B1(clk1_i),
    .B2(sel_i),
    .Y (clk_o)
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
