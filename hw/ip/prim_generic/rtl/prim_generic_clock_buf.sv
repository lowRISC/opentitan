// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_generic_clock_buf #(
  // Turning off these verilator lints because keeping these parameters makes it consistent with
  // the IP in hw/ip/prim_xilinx/rtl/ .
  /* verilator lint_off UNUSED */
  parameter bit NoFpgaBuf = 1'b0, // serves no function in generic
  parameter bit RegionSel = 1'b0  // serves no function in generic
  /* verilator lint_on UNUSED */
) (
  input clk_i,
  output logic clk_o
);

  logic inv;
  assign inv = ~clk_i;
  assign clk_o = ~inv;

endmodule // prim_generic_clock_buf
