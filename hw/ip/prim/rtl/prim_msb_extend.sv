// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Extend the output with the msb of the input

`include "prim_assert.sv"

module prim_msb_extend # (
  parameter int InWidth = 2,
  parameter int OutWidth = 2
) (
  input [InWidth-1:0] in_i,
  output [OutWidth-1:0] out_o
);

  `ASSERT_INIT(WidthCheck_A, OutWidth >= InWidth)

  localparam int WidthDiff = OutWidth - InWidth;

  if (WidthDiff == 0) begin : gen_feedthru
    assign out_o = in_i;
  end else begin : gen_tieoff
    assign out_o = {{WidthDiff{in_i[InWidth-1]}}, in_i};
  end

endmodule
