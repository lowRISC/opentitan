// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_xor2 #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in0_i,
  input  logic [Width-1:0] in1_i,
  output logic [Width-1:0] out_o
);

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    sg13cmos5l_xor2_1 u_xor (
      .A(in0_i[idx]),
      .B(in1_i[idx]),
      .X(out_o[idx])
    );
  end

endmodule
