// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Dummy clock gating module compatible with latch-based register file

module prim_clock_gating (
    input        clk_i,
    input        en_i,
    input        test_en_i,
    output logic clk_o
);

  logic clk_en;

  always_latch begin
    if (clk_i == 1'b0) begin
      clk_en <= en_i | test_en_i;
    end
  end

  assign clk_o = clk_i & clk_en;

endmodule
