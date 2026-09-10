// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Combinational buffer with enable signal. There is no suitable primitive at present.

module i3c_buf_en #(
  parameter int Width = 1,
  parameter logic [Width-1:0] OutDisabled = {Width{1'b1}}
) (
  input                    en_i,
  input        [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  logic [Width-1:0] out_int;
  prim_buf #(.Width(Width)) u_buf (
    .in_i (in_i),
    .out_o(out_int)
  );

  assign out_o = en_i ? out_int : OutDisabled;

endmodule
