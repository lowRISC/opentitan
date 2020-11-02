// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Slicer chops the incoming bitstring into OutW granularity.
// It supports fractional InW/OutW which fills 0 at the end of message.

`include "prim_assert.sv"

module prim_slicer #(
  parameter int InW = 64,
  parameter int OutW = 8,

  parameter int IndexW = 4
) (
  input        [IndexW-1:0] sel_i,
  input        [InW-1:0]    data_i,
  output logic [OutW-1:0]   data_o
);

  localparam int UnrollW = OutW*(2**IndexW);

  logic [UnrollW-1:0] unrolled_data;

  assign unrolled_data = UnrollW'(data_i);

  assign data_o = unrolled_data[sel_i*OutW+:OutW];

  `ASSERT_INIT(ValidWidth_A, InW <= OutW*(2**IndexW))

endmodule

