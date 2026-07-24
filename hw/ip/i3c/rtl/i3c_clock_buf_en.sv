// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Combinational clock buffer with enable signal with enable input and scan chain support.
// There is no suitable primitive at present.

module i3c_clock_buf_en #(
  parameter bit OutDisabled = 1'b0,  // output state when disabled.
  parameter bit NoFpgaBufG  = 1'b0   // only used in FPGA case
) (
  input  en_i,
  input  clk_i,
  input  scanmode_i,
  input  scan_clk_i,
  output clk_o
);

  // Buffered input clock.
  logic clk_buf, clk_gated;
  prim_clock_buf #(
    .NoFpgaBuf (NoFpgaBufG)
  ) u_buf (
    .clk_i(clk_i),
    .clk_o(clk_buf)
  );

  // Gated input clock.
  assign clk_gated = en_i ? clk_buf : OutDisabled;

  // Scan chain clocking.
  prim_clock_mux2 #(
    .NoFpgaBufG (NoFpgaBufG)
  ) u_mux (
    .clk0_i(clk_gated),
    .clk1_i(scan_clk_i),
    .sel_i (scanmode_i),
    .clk_o (clk_o)
  );

endmodule
