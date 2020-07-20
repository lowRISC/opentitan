// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Common Library: Clock Gating cell with synchronizer

module prim_clock_gating_sync (
  input        clk_i,
  input        rst_ni,
  input        test_en_i,
  input        async_en_i,
  output logic en_o,
  output logic clk_o
);


  prim_flop_2sync #(
    .Width(1)
  ) i_sync (
    .clk_i,
    .rst_ni,
    .d_i(async_en_i),
    .q_o(en_o)
  );

  prim_clock_gating i_cg (
    .clk_i,
    .en_i(en_o),
    .test_en_i,
    .clk_o
  );


endmodule
