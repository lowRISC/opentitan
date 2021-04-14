// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_xilinx_xor2 #(
  parameter int Width = 1
) (
  input [Width-1:0] in0_i,
  input [Width-1:0] in1_i,
  // Prevent Vivado from optimizing this signal away.
  (* keep = "true" *) output logic [Width-1:0] out_o
);

  assign out_o = in0_i ^ in1_i;

endmodule
