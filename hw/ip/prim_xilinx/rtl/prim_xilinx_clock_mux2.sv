// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_xilinx_clock_mux2 #(
  parameter bit NoFpgaBufG = 1'b0
) (
  input        clk0_i,
  input        clk1_i,
  input        sel_i,
  output logic clk_o
);

  if (NoFpgaBufG) begin : gen_no_bufg
    assign clk_o = (sel_i) ? clk1_i : clk0_i;
  end else begin : gen_bufg
    // for more info, refer to the Xilinx technology primitives userguide, e.g.:
    // ug953-vivado-7series-libraries.pdf
    // ug974-vivado-ultrascale-libraries.pdf
    BUFGMUX bufgmux_i (
      .S (sel_i),
      .I0(clk0_i),
      .I1(clk1_i),
      .O (clk_o)
    );
  end

  // make sure sel is never X (including during reset)
  // need to use ##1 as this could break with inverted clocks that
  // start with a rising edge at the beginning of the simulation.
  `ASSERT(selKnown0, ##1 !$isunknown(sel_i), clk0_i, 0)
  `ASSERT(selKnown1, ##1 !$isunknown(sel_i), clk1_i, 0)

endmodule : prim_xilinx_clock_mux2
