// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_generic_flop_en #(
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input                    clk_i,
  input                    rst_ni,
  // This is irrelevant for the generic model.
  // In the ASIC version, this may be used to bypass
  // the clock gate, in case the enable flop has to be
  // constructed using a clock gate and a normal flop.
  input                    test_en_i,
  input                    en_i,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic unused_test_en;
  assign unused_test_en = test_en_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      q_o <= ResetValue;
    end else if (en_i) begin
      q_o <= d_i;
    end
  end

endmodule
