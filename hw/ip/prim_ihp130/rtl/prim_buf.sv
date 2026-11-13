// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_buf #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    sg13cmos5l_buf_1 u_buf (
      .A(in_i[idx]),
      .X(out_o[idx])
    );
  end

endmodule
