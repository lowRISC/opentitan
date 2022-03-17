// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Convenience module for wrapping prim_and2 for use in blanking.
// When en_i == 1 the input is fed through to the output.
// When en_i == 0 the output is 0.
module prim_blanker #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in_i,
  input  logic             en_i,
  output logic [Width-1:0] out_o
);
  prim_and2 #(.Width(Width)) u_blank_and (
    .in0_i(in_i),
    .in1_i({Width{en_i}}),
    .out_o
  );
endmodule
