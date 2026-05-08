// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_inv #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    INVx2_ASAP7_75t_R u_size_only_inv (
      .A(in_i[idx]),
      .Y(out_o[idx])
    );
  end

endmodule
