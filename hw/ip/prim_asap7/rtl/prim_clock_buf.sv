// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_clock_buf #(
  // Turning off these verilator lints because keeping these parameters makes it consistent with
  // the IP in hw/ip/prim_xilinx/rtl/ .
  /* verilator lint_off UNUSED */
  parameter bit NoFpgaBuf = 1'b0, // serves no function in generic
  parameter bit RegionSel = 1'b0  // serves no function in generic
  /* verilator lint_on UNUSED */
) (
  input  logic clk_i,
  output logic clk_o
);

  // no special clock buffers available in this technology, use normal buffer
  BUFx2_ASAP7_75t_R u_size_only_buf (
    .A(clk_i),
    .Y(clk_o)
  );

endmodule // prim_clock_buf
