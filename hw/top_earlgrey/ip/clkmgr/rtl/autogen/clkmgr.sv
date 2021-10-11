// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The overall clock manager

`include "prim_assert.sv"

  module clkmgr
    import clkmgr_pkg::*;
    import clkmgr_reg_pkg::*;
    import lc_ctrl_pkg::lc_tx_t;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Primary module control clocks and resets
  // This drives the register interface
  input clk_i,
  input rst_ni,

  // System clocks and resets
  // These are the source clocks for the system
  input clk_main_i,
  input rst_main_ni,
  input clk_io_i,
  input rst_io_ni,
  input clk_usb_i,
  input rst_usb_ni,
  input clk_aon_i,
  input rst_aon_ni,

  // Resets for derived clocks
  // clocks are derived locally
  input rst_io_div2_ni,
  input rst_io_div4_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_clk_req_t pwr_i,
  output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,

  // dft interface
  input lc_tx_t scanmode_i,

  // idle hints
  input [4:0] idle_i,

  // life cycle state output
  input lc_tx_t lc_dft_en_i,

  // clock bypass control
  input lc_tx_t lc_clk_byp_req_i,
  output lc_tx_t ast_clk_byp_req_o,
  input lc_tx_t ast_clk_byp_ack_i,
  output lc_tx_t lc_clk_byp_ack_o,

  // jittery enable
  output logic jitter_en_o,

  // clock gated indications going to alert handlers
  output clkmgr_cg_en_t cg_en_o,

  // clock output interface
  output clkmgr_out_t clocks_o

);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  ////////////////////////////////////////////////////
  // Divided clocks
  ////////////////////////////////////////////////////

  lc_tx_t step_down_req;
  logic [1:0] step_down_acks;

  logic clk_io_div2_i;
  logic clk_io_div4_i;


  lc_tx_t io_div2_div_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div2_div_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(io_div2_div_scanmode)
  );

  prim_clock_div #(
    .Divisor(2)
  ) u_no_scan_io_div2_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .step_down_req_i(step_down_req == lc_ctrl_pkg::On),
    .step_down_ack_o(step_down_acks[0]),
    .test_en_i(io_div2_div_scanmode == lc_ctrl_pkg::On),
    .clk_o(clk_io_div2_i)
  );

  lc_tx_t io_div4_div_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div4_div_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(io_div4_div_scanmode)
  );

  prim_clock_div #(
    .Divisor(4)
  ) u_no_scan_io_div4_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .step_down_req_i(step_down_req == lc_ctrl_pkg::On),
    .step_down_ack_o(step_down_acks[1]),
    .test_en_i(io_div4_div_scanmode == lc_ctrl_pkg::On),
    .clk_o(clk_io_div4_i)
  );

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  logic [NumAlerts-1:0] alert_test, alerts;
  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  clkmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .clk_io_i,
    .rst_io_ni,
    .clk_io_div2_i,
    .rst_io_div2_ni,
    .clk_io_div4_i,
    .rst_io_div4_ni,
    .clk_main_i,
    .rst_main_ni,
    .clk_usb_i,
    .rst_usb_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(hw2reg.fatal_err_code.de),
    .devmode_i(1'b1)
  );
  assign hw2reg.fatal_err_code.d = 1'b1;


  ////////////////////////////////////////////////////
  // Alerts
  ////////////////////////////////////////////////////

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_fault.q & reg2hw.alert_test.recov_fault.qe
  };

  logic recov_alert;
  assign recov_alert =
    hw2reg.recov_err_code.io_measure_err.de |
    hw2reg.recov_err_code.io_div2_measure_err.de |
    hw2reg.recov_err_code.io_div4_measure_err.de |
    hw2reg.recov_err_code.main_measure_err.de |
    hw2reg.recov_err_code.usb_measure_err.de;

  assign alerts = {
    |reg2hw.fatal_err_code,
    recov_alert
  };

  localparam logic [NumAlerts-1:0] AlertFatal = {1'b1, 1'b0};

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(AlertFatal[i])
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////////////////////////////////////////
  // Clock bypass request
  ////////////////////////////////////////////////////

  clkmgr_byp #(
    .NumDivClks(2)
  ) u_clkmgr_byp (
    .clk_i,
    .rst_ni,
    .en_i(lc_dft_en_i),
    .byp_req_i(lc_tx_t'(reg2hw.extclk_ctrl.sel.q)),
    .step_down_req_i(lc_tx_t'(reg2hw.extclk_ctrl.step_down.q)),
    .ast_clk_byp_req_o,
    .ast_clk_byp_ack_i,
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .step_down_acks_i(step_down_acks),
    .step_down_req_o(step_down_req)
  );

  ////////////////////////////////////////////////////
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
  prim_clock_buf u_clk_io_div4_powerup_buf (
    .clk_i(clk_io_div4_i),
    .clk_o(clocks_o.clk_io_div4_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.io_div4_powerup = MuBi4False;
  prim_clock_buf u_clk_aon_powerup_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_powerup = MuBi4False;
  prim_clock_buf u_clk_main_powerup_buf (
    .clk_i(clk_main_i),
    .clk_o(clocks_o.clk_main_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.main_powerup = MuBi4False;
  prim_clock_buf u_clk_io_powerup_buf (
    .clk_i(clk_io_i),
    .clk_o(clocks_o.clk_io_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.io_powerup = MuBi4False;
  prim_clock_buf u_clk_usb_powerup_buf (
    .clk_i(clk_usb_i),
    .clk_o(clocks_o.clk_usb_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.usb_powerup = MuBi4False;
  prim_clock_buf u_clk_io_div2_powerup_buf (
    .clk_i(clk_io_div2_i),
    .clk_o(clocks_o.clk_io_div2_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.io_div2_powerup = MuBi4False;
  prim_clock_buf u_clk_aon_infra_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_infra)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_infra = MuBi4False;
  prim_clock_buf u_clk_aon_secure_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_secure)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_secure = MuBi4False;
  prim_clock_buf u_clk_aon_peri_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_peri)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_peri = MuBi4False;
  prim_clock_buf u_clk_aon_timers_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_timers)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_timers = MuBi4False;

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  logic wait_enable;
  logic wait_disable;
  logic en_status_d;
  logic dis_status_d;
  logic [1:0] en_status_q;
  logic [1:0] dis_status_q;
  logic clk_status;
  logic clk_io_root;
  logic clk_io_en;
  logic clk_io_div2_root;
  logic clk_io_div2_en;
  logic clk_io_div4_root;
  logic clk_io_div4_en;
  logic clk_main_root;
  logic clk_main_en;
  logic clk_usb_root;
  logic clk_usb_en;

  lc_tx_t io_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(io_scanmode)
  );

  prim_clock_gating_sync u_io_cg (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .test_en_i(io_scanmode == lc_ctrl_pkg::On),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_io_en),
    .clk_o(clk_io_root)
  );

  lc_tx_t io_div2_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div2_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(io_div2_scanmode)
  );

  prim_clock_gating_sync u_io_div2_cg (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .test_en_i(io_div2_scanmode == lc_ctrl_pkg::On),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_io_div2_en),
    .clk_o(clk_io_div2_root)
  );

  lc_tx_t io_div4_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div4_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(io_div4_scanmode)
  );

  prim_clock_gating_sync u_io_div4_cg (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .test_en_i(io_div4_scanmode == lc_ctrl_pkg::On),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_io_div4_en),
    .clk_o(clk_io_div4_root)
  );

  lc_tx_t main_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_main_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(main_scanmode)
  );

  prim_clock_gating_sync u_main_cg (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .test_en_i(main_scanmode == lc_ctrl_pkg::On),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_main_en),
    .clk_o(clk_main_root)
  );

  lc_tx_t usb_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_usb_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(usb_scanmode)
  );

  prim_clock_gating_sync u_usb_cg (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .test_en_i(usb_scanmode == lc_ctrl_pkg::On),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_usb_en),
    .clk_o(clk_usb_root)
  );

  // an async AND of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are enabled
  assign wait_enable =
    clk_io_en &
    clk_io_div2_en &
    clk_io_div4_en &
    clk_main_en &
    clk_usb_en;

  // an async OR of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are disabled
  assign wait_disable =
    clk_io_en |
    clk_io_div2_en |
    clk_io_div4_en |
    clk_main_en |
    clk_usb_en;

  // Sync clkmgr domain for feedback to pwrmgr.
  // Since the signal is combo / converged on the other side, de-bounce
  // the signal prior to output
  prim_flop_2sync #(
    .Width(1)
  ) u_roots_en_status_sync (
    .clk_i,
    .rst_ni,
    .d_i(wait_enable),
    .q_o(en_status_d)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_roots_or_sync (
    .clk_i,
    .rst_ni,
    .d_i(wait_disable),
    .q_o(dis_status_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      en_status_q <= '0;
      dis_status_q <= '0;
      clk_status <= '0;
    end else begin
      en_status_q <= {en_status_q[0], en_status_d};
      dis_status_q <= {dis_status_q[0], dis_status_d};

      if (&en_status_q) begin
        clk_status <= 1'b1;
      end else if (|dis_status_q == '0) begin
        clk_status <= 1'b0;
      end
    end
  end

  assign pwr_o.clk_status = clk_status;

  ////////////////////////////////////////////////////
  // Clock Measurement for the roots
  ////////////////////////////////////////////////////

  logic io_fast_err;
  logic io_slow_err;
    prim_clock_meas #(
    .Cnt(960),
    .RefCnt(1)
  ) u_io_meas (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_io_en & reg2hw.io_measure_ctrl.en.q),
    .max_cnt(reg2hw.io_measure_ctrl.max_thresh.q),
    .min_cnt(reg2hw.io_measure_ctrl.min_thresh.q),
    .valid_o(),
    .fast_o(io_fast_err),
    .slow_o(io_slow_err)
  );

  logic synced_io_err;
  prim_pulse_sync u_io_err_sync (
    .clk_src_i(clk_io_i),
    .rst_src_ni(rst_io_ni),
    .src_pulse_i(io_fast_err | io_slow_err),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(synced_io_err)
  );

  assign hw2reg.recov_err_code.io_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_measure_err.de = synced_io_err;

  logic io_div2_fast_err;
  logic io_div2_slow_err;
    prim_clock_meas #(
    .Cnt(480),
    .RefCnt(1)
  ) u_io_div2_meas (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_io_div2_en & reg2hw.io_div2_measure_ctrl.en.q),
    .max_cnt(reg2hw.io_div2_measure_ctrl.max_thresh.q),
    .min_cnt(reg2hw.io_div2_measure_ctrl.min_thresh.q),
    .valid_o(),
    .fast_o(io_div2_fast_err),
    .slow_o(io_div2_slow_err)
  );

  logic synced_io_div2_err;
  prim_pulse_sync u_io_div2_err_sync (
    .clk_src_i(clk_io_div2_i),
    .rst_src_ni(rst_io_div2_ni),
    .src_pulse_i(io_div2_fast_err | io_div2_slow_err),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(synced_io_div2_err)
  );

  assign hw2reg.recov_err_code.io_div2_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div2_measure_err.de = synced_io_div2_err;

  logic io_div4_fast_err;
  logic io_div4_slow_err;
    prim_clock_meas #(
    .Cnt(240),
    .RefCnt(1)
  ) u_io_div4_meas (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_io_div4_en & reg2hw.io_div4_measure_ctrl.en.q),
    .max_cnt(reg2hw.io_div4_measure_ctrl.max_thresh.q),
    .min_cnt(reg2hw.io_div4_measure_ctrl.min_thresh.q),
    .valid_o(),
    .fast_o(io_div4_fast_err),
    .slow_o(io_div4_slow_err)
  );

  logic synced_io_div4_err;
  prim_pulse_sync u_io_div4_err_sync (
    .clk_src_i(clk_io_div4_i),
    .rst_src_ni(rst_io_div4_ni),
    .src_pulse_i(io_div4_fast_err | io_div4_slow_err),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(synced_io_div4_err)
  );

  assign hw2reg.recov_err_code.io_div4_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div4_measure_err.de = synced_io_div4_err;

  logic main_fast_err;
  logic main_slow_err;
    prim_clock_meas #(
    .Cnt(1000),
    .RefCnt(1)
  ) u_main_meas (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_main_en & reg2hw.main_measure_ctrl.en.q),
    .max_cnt(reg2hw.main_measure_ctrl.max_thresh.q),
    .min_cnt(reg2hw.main_measure_ctrl.min_thresh.q),
    .valid_o(),
    .fast_o(main_fast_err),
    .slow_o(main_slow_err)
  );

  logic synced_main_err;
  prim_pulse_sync u_main_err_sync (
    .clk_src_i(clk_main_i),
    .rst_src_ni(rst_main_ni),
    .src_pulse_i(main_fast_err | main_slow_err),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(synced_main_err)
  );

  assign hw2reg.recov_err_code.main_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.main_measure_err.de = synced_main_err;

  logic usb_fast_err;
  logic usb_slow_err;
    prim_clock_meas #(
    .Cnt(480),
    .RefCnt(1)
  ) u_usb_meas (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_usb_en & reg2hw.usb_measure_ctrl.en.q),
    .max_cnt(reg2hw.usb_measure_ctrl.max_thresh.q),
    .min_cnt(reg2hw.usb_measure_ctrl.min_thresh.q),
    .valid_o(),
    .fast_o(usb_fast_err),
    .slow_o(usb_slow_err)
  );

  logic synced_usb_err;
  prim_pulse_sync u_usb_err_sync (
    .clk_src_i(clk_usb_i),
    .rst_src_ni(rst_usb_ni),
    .src_pulse_i(usb_fast_err | usb_slow_err),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(synced_usb_err)
  );

  assign hw2reg.recov_err_code.usb_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.usb_measure_err.de = synced_usb_err;


  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
  assign clocks_o.clk_io_div4_infra = clk_io_div4_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div4_infra (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .mubi_i(((clk_io_div4_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div4_infra)
  );
  assign clocks_o.clk_main_infra = clk_main_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_infra (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_infra)
  );
  assign clocks_o.clk_io_div4_secure = clk_io_div4_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div4_secure (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .mubi_i(((clk_io_div4_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div4_secure)
  );
  assign clocks_o.clk_main_secure = clk_main_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_secure (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_secure)
  );
  assign clocks_o.clk_usb_secure = clk_usb_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_usb_secure (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .mubi_i(((clk_usb_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.usb_secure)
  );
  assign clocks_o.clk_io_div4_timers = clk_io_div4_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div4_timers (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .mubi_i(((clk_io_div4_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div4_timers)
  );

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

  logic clk_io_div4_peri_sw_en;
  logic clk_io_div2_peri_sw_en;
  logic clk_io_peri_sw_en;
  logic clk_usb_peri_sw_en;

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_div4_peri_sw_en_sync (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .d_i(reg2hw.clk_enables.clk_io_div4_peri_en.q),
    .q_o(clk_io_div4_peri_sw_en)
  );

  lc_tx_t clk_io_div4_peri_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div4_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_io_div4_peri_scanmode)
  );

  logic clk_io_div4_peri_combined_en;
  assign clk_io_div4_peri_combined_en = clk_io_div4_peri_sw_en & clk_io_div4_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_div4_peri_cg (
    .clk_i(clk_io_div4_root),
    .en_i(clk_io_div4_peri_combined_en),
    .test_en_i(clk_io_div4_peri_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_io_div4_peri)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div4_peri (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .mubi_i(((clk_io_div4_peri_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div4_peri)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_div2_peri_sw_en_sync (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .d_i(reg2hw.clk_enables.clk_io_div2_peri_en.q),
    .q_o(clk_io_div2_peri_sw_en)
  );

  lc_tx_t clk_io_div2_peri_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div2_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_io_div2_peri_scanmode)
  );

  logic clk_io_div2_peri_combined_en;
  assign clk_io_div2_peri_combined_en = clk_io_div2_peri_sw_en & clk_io_div2_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_div2_peri_cg (
    .clk_i(clk_io_div2_root),
    .en_i(clk_io_div2_peri_combined_en),
    .test_en_i(clk_io_div2_peri_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_io_div2_peri)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div2_peri (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .mubi_i(((clk_io_div2_peri_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div2_peri)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_peri_sw_en_sync (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .d_i(reg2hw.clk_enables.clk_io_peri_en.q),
    .q_o(clk_io_peri_sw_en)
  );

  lc_tx_t clk_io_peri_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_io_peri_scanmode)
  );

  logic clk_io_peri_combined_en;
  assign clk_io_peri_combined_en = clk_io_peri_sw_en & clk_io_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_peri_cg (
    .clk_i(clk_io_root),
    .en_i(clk_io_peri_combined_en),
    .test_en_i(clk_io_peri_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_io_peri)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_peri (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .mubi_i(((clk_io_peri_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_peri)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_usb_peri_sw_en_sync (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .d_i(reg2hw.clk_enables.clk_usb_peri_en.q),
    .q_o(clk_usb_peri_sw_en)
  );

  lc_tx_t clk_usb_peri_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_usb_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_usb_peri_scanmode)
  );

  logic clk_usb_peri_combined_en;
  assign clk_usb_peri_combined_en = clk_usb_peri_sw_en & clk_usb_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_usb_peri_cg (
    .clk_i(clk_usb_root),
    .en_i(clk_usb_peri_combined_en),
    .test_en_i(clk_usb_peri_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_usb_peri)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_usb_peri (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .mubi_i(((clk_usb_peri_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.usb_peri)
  );


  ////////////////////////////////////////////////////
  // Software hint group
  // The idle hint feedback is assumed to be synchronous to the
  // clock target
  ////////////////////////////////////////////////////

  logic clk_main_aes_hint;
  logic clk_main_aes_en;
  logic clk_main_hmac_hint;
  logic clk_main_hmac_en;
  logic clk_main_kmac_hint;
  logic clk_main_kmac_en;
  logic clk_main_otbn_hint;
  logic clk_main_otbn_en;
  logic clk_io_div4_otbn_hint;
  logic clk_io_div4_otbn_en;

  assign clk_main_aes_en = clk_main_aes_hint | ~idle_i[HintMainAes];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_aes_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_aes_hint.q),
    .q_o(clk_main_aes_hint)
  );

  lc_tx_t clk_main_aes_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_aes_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_main_aes_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_main_aes_combined_en;
  prim_buf u_prim_buf_clk_main_aes_en (
    .in_i(clk_main_aes_en & clk_main_en),
    .out_o(clk_main_aes_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_aes_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_aes_combined_en),
    .test_en_i(clk_main_aes_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_main_aes)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_aes (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_aes_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_aes)
  );

  assign clk_main_hmac_en = clk_main_hmac_hint | ~idle_i[HintMainHmac];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_hmac_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_hmac_hint.q),
    .q_o(clk_main_hmac_hint)
  );

  lc_tx_t clk_main_hmac_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_hmac_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_main_hmac_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_main_hmac_combined_en;
  prim_buf u_prim_buf_clk_main_hmac_en (
    .in_i(clk_main_hmac_en & clk_main_en),
    .out_o(clk_main_hmac_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_hmac_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_hmac_combined_en),
    .test_en_i(clk_main_hmac_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_main_hmac)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_hmac (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_hmac_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_hmac)
  );

  assign clk_main_kmac_en = clk_main_kmac_hint | ~idle_i[HintMainKmac];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_kmac_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_kmac_hint.q),
    .q_o(clk_main_kmac_hint)
  );

  lc_tx_t clk_main_kmac_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_kmac_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_main_kmac_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_main_kmac_combined_en;
  prim_buf u_prim_buf_clk_main_kmac_en (
    .in_i(clk_main_kmac_en & clk_main_en),
    .out_o(clk_main_kmac_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_kmac_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_kmac_combined_en),
    .test_en_i(clk_main_kmac_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_main_kmac)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_kmac (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_kmac_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_kmac)
  );

  assign clk_main_otbn_en = clk_main_otbn_hint | ~idle_i[HintMainOtbn];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_otbn_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_otbn_hint.q),
    .q_o(clk_main_otbn_hint)
  );

  lc_tx_t clk_main_otbn_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_otbn_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_main_otbn_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_main_otbn_combined_en;
  prim_buf u_prim_buf_clk_main_otbn_en (
    .in_i(clk_main_otbn_en & clk_main_en),
    .out_o(clk_main_otbn_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_otbn_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_otbn_combined_en),
    .test_en_i(clk_main_otbn_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_main_otbn)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_otbn (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_otbn_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_otbn)
  );

  assign clk_io_div4_otbn_en = clk_io_div4_otbn_hint | ~idle_i[HintIoDiv4Otbn];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_div4_otbn_hint_sync (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .d_i(reg2hw.clk_hints.clk_io_div4_otbn_hint.q),
    .q_o(clk_io_div4_otbn_hint)
  );

  lc_tx_t clk_io_div4_otbn_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div4_otbn_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(clk_io_div4_otbn_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_io_div4_otbn_combined_en;
  prim_buf u_prim_buf_clk_io_div4_otbn_en (
    .in_i(clk_io_div4_otbn_en & clk_io_div4_en),
    .out_o(clk_io_div4_otbn_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_io_div4_otbn_cg (
    .clk_i(clk_io_div4_root),
    .en_i(clk_io_div4_otbn_combined_en),
    .test_en_i(clk_io_div4_otbn_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.clk_io_div4_otbn)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div4_otbn (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .mubi_i(((clk_io_div4_otbn_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div4_otbn)
  );


  // state readback
  assign hw2reg.clk_hints_status.clk_main_aes_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_aes_val.d = clk_main_aes_en;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.d = clk_main_hmac_en;
  assign hw2reg.clk_hints_status.clk_main_kmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_kmac_val.d = clk_main_kmac_en;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.d = clk_main_otbn_en;
  assign hw2reg.clk_hints_status.clk_io_div4_otbn_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_io_div4_otbn_val.d = clk_io_div4_otbn_en;

  assign jitter_en_o = reg2hw.jitter_enable.q;

  ////////////////////////////////////////////////////
  // Exported clocks
  ////////////////////////////////////////////////////


  ////////////////////////////////////////////////////
  // Assertions
  ////////////////////////////////////////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(AlertsKnownO_A,   alert_tx_o)
  `ASSERT_KNOWN(PwrMgrKnownO_A, pwr_o)
  `ASSERT_KNOWN(AstClkBypReqKnownO_A, ast_clk_byp_req_o)
  `ASSERT_KNOWN(LcCtrlClkBypAckKnownO_A, lc_clk_byp_ack_o)
  `ASSERT_KNOWN(JitterEnableKnownO_A, jitter_en_o)
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)
  `ASSERT_KNOWN(CgEnKnownO_A, cg_en_o)

endmodule // clkmgr
