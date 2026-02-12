// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_clock_inv #(
  parameter bit HasScanMode = 1'b1,
  parameter bit NoFpgaBufG  = 1'b0 // only used in FPGA case
) (
  input  logic clk_i,
  input  logic scanmode_i,
  output logic clk_no      // Inverted
);

  // an XOR only inverts the clock if scanmode_i=0
  XOR2x1_ASAP7_75t_R u_size_only_xor (
    .A(clk_i),
    .B(~scanmode_i),
    .Y(clk_no)
  );

  `ASSERT(scanmodeKnown, ##1 !$isunknown(scanmode_i), clk_no, 0)

endmodule : prim_clock_inv
