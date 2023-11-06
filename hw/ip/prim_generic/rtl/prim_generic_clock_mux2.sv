// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_clock_mux2 #(
  parameter bit NoFpgaBufG = 1'b0 // this parameter serves no function in the generic model
) (
  input        clk0_i,
  input        clk1_i,
  input        sel_i,
  output logic clk_o
);
`ifdef TARGET_ASIC
  tc_clk_mux2 clk_mux(
    .clk0_i,
    .clk1_i,
    .clk_sel_i(sel_i),
    .clk_o
  );
`else
  // We model the mux with logic operations for GTECH runs.
  assign clk_o = (sel_i & clk1_i) | (~sel_i & clk0_i);

  // make sure sel is never X (including during reset)
  // need to use ##1 as this could break with inverted clocks that
  // start with a rising edge at the beginning of the simulation.
`endif
endmodule : prim_clock_mux2
