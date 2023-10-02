// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Clock inverter
//   Varies on the process

module prim_clock_inv #(
  parameter bit HasScanMode = 1'b1,
  parameter bit NoFpgaBufG  = 1'b0 // only used in FPGA case
) (
  input        clk_i,
  input        scanmode_i,
  output logic clk_no      // Inverted
);

  tc_clk_inverter clk_inv(
   .clk_i,
   .clk_o(clk_no)
  );

endmodule : prim_clock_inv
