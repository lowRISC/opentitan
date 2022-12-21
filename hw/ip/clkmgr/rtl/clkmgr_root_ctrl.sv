// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Wrapper for scan sync and clock gating cell

module clkmgr_root_ctrl
  import clkmgr_pkg::*;
  import prim_mubi_pkg::mubi4_t;
(
  input clk_i,
  input rst_ni,

  input mubi4_t scanmode_i,
  input async_en_i,

  output logic en_o,
  output logic clk_o
);

  mubi4_t scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0) // clock/reset below is only used for SVAs.
  ) u_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o({scanmode})
  );

  prim_clock_gating_sync u_cg (
    .clk_i,
    .rst_ni,
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode)),
    .async_en_i,
    .en_o,
    .clk_o
  );

endmodule // clkmgr_root_ctrl
