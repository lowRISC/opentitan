// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// One-hot decoder
// Outputs a binary encoded version of an one-hot encoded input.

`include "prim_assert.sv"

module prim_onehot_dec #(
  parameter int unsigned OneHotWidth  = 32,
  localparam int unsigned OutputWidth = $clog2(OneHotWidth)
) (
  input  logic                   clk_i,   // used for SVAs only
  input  logic                   rst_ni,  // used for SVAs only
  input  logic [OneHotWidth-1:0] in_i,
  output logic [OutputWidth-1:0] out_o
);
  localparam int unsigned MASK_WIDTH = 2**OutputWidth;

  logic [MASK_WIDTH-1:0] inp_padded;

  // Pad one-hot encoded input value to the next power of 2
  assign inp_padded = {{(MASK_WIDTH - OneHotWidth){1'b0}}, in_i };
  // Priority encoder to convert one-hot to binary
  for (genvar i = 0; i < OutputWidth; ++i) begin : g_priority_encoder
      logic [2*(2**i)-1:0]   submask;
      logic [MASK_WIDTH-1:0] decoding_mask;

      assign submask       = { {(2**i){1'b1}}, {(2**i){1'b0}} };
      assign decoding_mask = { (2**(OutputWidth - 1 - i)) {submask} };
      assign out_o[i]      = |(inp_padded & decoding_mask);
  end : g_priority_encoder

  // Assertions
  `ASSERT(CheckHotOne_A, $onehot(in_i))
endmodule
