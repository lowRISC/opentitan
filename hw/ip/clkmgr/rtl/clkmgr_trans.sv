// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Handle clock manager transactional clocks

module clkmgr_trans
  import clkmgr_pkg::*;
  import prim_mubi_pkg::mubi4_t;
# (
  parameter bit FpgaBufGlobal = 1
) (
  input clk_i,
  input rst_ni,
  input clk_root_i,
  input clk_root_en_i,
  input mubi4_t idle_i,
  input sw_hint_i,
  input mubi4_t scanmode_i,
  output mubi4_t alert_cg_en_o,
  output logic clk_o,
  output logic clk_en_o,
  output logic cnt_err_o
);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_false_loose;

  // Note this value is specifically chosen.
  // The binary value is 1010, which is a balanced 4-bit value
  // that should in theory be resistant to all 0 or all 1 attacks.
  localparam int TransIdleCnt = 10;
  localparam int IdleCntWidth = $clog2(TransIdleCnt + 1);

  logic [IdleCntWidth-1:0] idle_cnt;
  logic idle_valid;
  logic sw_hint_synced;
  assign idle_valid = (idle_cnt == TransIdleCnt);
  assign clk_en_o = sw_hint_synced | ~idle_valid;

  prim_flop_2sync #(
    .Width(1)
  ) u_hint_sync (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(sw_hint_i),
    .q_o(sw_hint_synced)
  );

  // SEC_CM: IDLE.CTR.REDUN
  prim_count #(
    .Width(IdleCntWidth),
    .OutSelDnCnt('0),
    .CntStyle(prim_count_pkg::DupCnt)
  ) u_idle_cnt (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    // the default condition is to keep the clock enabled
    .clr_i(mubi4_test_false_loose(idle_i)),
    .set_i('0),
    .set_cnt_i('0),
    .en_i(mubi4_test_true_strict(idle_i) & ~idle_valid),
    .step_i(IdleCntWidth'(1'b1)),
    .cnt_o(idle_cnt),
    .err_o(cnt_err_o)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_scanmode_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_combined_en;
  prim_buf u_prim_buf_en (
    .in_i(clk_en_o & clk_root_en_i),
    .out_o(clk_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(FpgaBufGlobal)
  ) u_cg (
    .clk_i(clk_root_i),
    .en_i(clk_combined_en),
    .test_en_i(mubi4_test_true_strict(scanmode[0])),
    .clk_o(clk_o)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .mubi_i(clk_combined_en ? MuBi4False : MuBi4True),
    .mubi_o(alert_cg_en_o)
  );

endmodule
