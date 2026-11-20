// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_inv #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  assign out_o = ~in_i;

endmodule
