// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Prevent Vivado from performing optimizations on/across this module.
(* DONT_TOUCH = "yes" *)
module prim_xilinx_buf #(
  parameter int Width = 1
) (
  input [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  assign out_o = in_i;

endmodule
