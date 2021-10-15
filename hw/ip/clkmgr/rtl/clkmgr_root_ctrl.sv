// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Wrapper for scan sync and clock gating cell

module clkmgr_root_ctrl
  import clkmgr_pkg::*;
  import lc_ctrl_pkg::lc_tx_t;
(
  input clk_i,
  input rst_ni,

  input lc_tx_t scanmode_i,
  input async_en_i,

  output logic en_o,
  output logic clk_o
);

  lc_tx_t scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(scanmode)
  );

  prim_clock_gating_sync u_cg (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .test_en_i(scanmode == lc_ctrl_pkg::On),
    .async_en_i,
    .en_o,
    .clk_o
  );

endmodule // clkmgr_root_ctrl
