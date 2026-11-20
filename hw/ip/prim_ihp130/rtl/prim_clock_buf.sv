// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_clock_buf #(
  // Turning off these verilator lints because keeping these parameters makes it consistent with
  // the IP in hw/ip/prim_xilinx/rtl/ .
  /* verilator lint_off UNUSED */
  parameter bit NoFpgaBuf = 1'b0, // serves no function in IHP130
  parameter bit RegionSel = 1'b0  // serves no function in IHP130
  /* verilator lint_on UNUSED */
) (
  input  logic clk_i,
  output logic clk_o
);

  // no special clock buffers available in this technology, use normal buffer
  sg13cmos5l_buf_1 u_clock_buf (
    .A(clk_i),
    .X(clk_o)
  );

endmodule // prim_clock_buf
