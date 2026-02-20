// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_sec_anchor_const #(
  parameter int Width = 1,
  parameter logic [Width-1:0] ConstVal = '0
) (
  output logic [Width-1:0] out_o
);

  prim_const_sec #(
    .Width(Width),
    .ConstVal(ConstVal)
  ) u_secure_anchor_const (
    .out_o
  );

endmodule
