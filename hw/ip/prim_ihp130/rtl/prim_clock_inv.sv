// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_clock_inv #(
  parameter bit HasScanMode = 1'b1,
  parameter bit NoFpgaBufG  = 1'b0
) (
  input  logic clk_i,
  input  logic scanmode_i,
  output logic clk_no
);

  if (HasScanMode) begin : gen_scan
    // Inverted clock on A0, pass-through on A1 for scan.
    sg13cmos5l_mux2_1 u_clock_inv_mux (
      .A0(~clk_i),
      .A1( clk_i),
      .S (scanmode_i),
      .X (clk_no)
    );
  end else begin : gen_noscan
    logic unused_scanmode;
    assign unused_scanmode = scanmode_i;

    sg13cmos5l_inv_1 u_clock_inv (
      .A(clk_i),
      .Y(clk_no)
    );
  end

  `ASSERT(scanmodeKnown, ##1 !$isunknown(scanmode_i), clk_i, 0)

endmodule : prim_clock_inv
