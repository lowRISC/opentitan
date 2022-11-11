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
  input clk_gated_i,
  input rst_ni,
  input en_i,
  input mubi4_t idle_i,
  input sw_hint_i,
  input mubi4_t scanmode_i,
  output mubi4_t alert_cg_en_o,
  output logic clk_o,

  // interface to regfile
  input clk_reg_i,
  input rst_reg_ni,
  output logic reg_en_o,
  output logic reg_cnt_err_o
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
  logic local_en;
  assign idle_valid = (idle_cnt == TransIdleCnt);
  assign local_en = sw_hint_synced | ~idle_valid;

  prim_flop_2sync #(
    .Width(1)
  ) u_hint_sync (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(sw_hint_i),
    .q_o(sw_hint_synced)
  );

  // Idle sync: Idle signal comes from IP module. The reset of the Idle signal
  // may differ from the reset here. Adding mubi sync to synchronize.
  prim_mubi_pkg::mubi4_t [0:0] idle;
  prim_mubi4_sync #(
    .NumCopies      ( 1     ),
    .AsyncOn        ( 1'b 1 ),
    .StabilityCheck ( 1'b 1 )
  ) u_idle_sync (
    .clk_i,
    .rst_ni,
    .mubi_i (idle_i),
    .mubi_o (idle)
  );

  // SEC_CM: IDLE.CTR.REDUN
  logic cnt_err;
  prim_count #(
    .Width(IdleCntWidth)
  ) u_idle_cnt (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    // the default condition is to keep the clock enabled
    .clr_i(mubi4_test_false_loose(idle[0])),
    .set_i('0),
    .set_cnt_i('0),
    .incr_en_i(mubi4_test_true_strict(idle[0]) & ~idle_valid),
    .decr_en_i(1'b0),
    .step_i(IdleCntWidth'(1'b1)),
    .cnt_o(idle_cnt),
    .cnt_next_o(),
    .err_o(cnt_err)
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
  logic combined_en_d, combined_en_q;
  prim_buf u_prim_buf_en (
    .in_i(local_en & en_i),
    .out_o(combined_en_d)
  );

  // clk_gated_i is already controlled by en_i, so there is no need
  // to use it in the below gating function
  prim_clock_gating #(
    .FpgaBufGlobal(FpgaBufGlobal)
  ) u_cg (
    .clk_i(clk_gated_i),
    .en_i(local_en),
    .test_en_i(mubi4_test_true_strict(scanmode[0])),
    .clk_o(clk_o)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .mubi_i(combined_en_d ? MuBi4False : MuBi4True),
    .mubi_o(alert_cg_en_o)
  );

  // we hold the error because there is no guarantee on
  // what the timing of cnt_err looks like, it may be a
  // pulse or it may be level.  If it's for former,
  // prim_sync_reqack may miss it, if it's the latter,
  // prim_pulse_sync may miss it.  As a result, just
  // latch forever and sync it over.
  logic hold_err;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      hold_err <= '0;
    end else if (cnt_err) begin
      hold_err <= 1'b1;
    end
  end

  // register facing domain
  prim_flop_2sync #(
    .Width(1)
  ) u_err_sync (
    .clk_i(clk_reg_i),
    .rst_ni(rst_reg_ni),
    .d_i(hold_err),
    .q_o(reg_cnt_err_o)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      combined_en_q <= '0;
    end else begin
      combined_en_q <= combined_en_d;
    end
  end

  prim_flop_2sync #(
    .Width(1)
  ) u_en_sync (
    .clk_i(clk_reg_i),
    .rst_ni(rst_reg_ni),
    .d_i(combined_en_q),
    .q_o(reg_en_o)
  );


endmodule
