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
    import prim_mubi_pkg::mubi4_t;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Primary module control clocks and resets
  // This drives the register interface
  input clk_i,
  input rst_ni,
  input rst_shadowed_ni,

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
  input prim_mubi_pkg::mubi4_t scanmode_i,

  // idle hints
  input [4:0] idle_i,

  // life cycle state output
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input lc_tx_t lc_hw_debug_en_i,

  // clock bypass control with lc_ctrl
  // SEC_CM: LC_CTRL_CLK_HANDSHAKE.INTERSIG.MUBI
  input lc_tx_t lc_clk_byp_req_i,
  output lc_tx_t lc_clk_byp_ack_o,

  // clock bypass control with ast
  // SEC_CM: CLK_HANDSHAKE.INTERSIG.MUBI
  output mubi4_t io_clk_byp_req_o,
  input mubi4_t io_clk_byp_ack_i,
  output mubi4_t all_clk_byp_req_o,
  input mubi4_t all_clk_byp_ack_i,
  output logic hi_speed_sel_o,

  // jittery enable
  output logic jitter_en_o,

  // clock gated indications going to alert handlers
  output clkmgr_cg_en_t cg_en_o,

  // clock output interface
  output clkmgr_out_t clocks_o

);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::mubi4_test_false_loose;

  ////////////////////////////////////////////////////
  // Divided clocks
  ////////////////////////////////////////////////////

  logic step_down_req;
  logic [1:0] step_down_acks;

  logic clk_io_div2_i;
  logic clk_io_div4_i;

  logic io_step_down_req;
  prim_flop_2sync #(
    .Width(1)
  ) u_io_step_down_req_sync (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .d_i(step_down_req),
    .q_o(io_step_down_req)
  );


  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] io_div2_div_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div2_div_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(io_div2_div_scanmode)
  );

  prim_clock_div #(
    .Divisor(2)
  ) u_no_scan_io_div2_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .step_down_req_i(io_step_down_req),
    .step_down_ack_o(step_down_acks[0]),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(io_div2_div_scanmode[0])),
    .clk_o(clk_io_div2_i)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] io_div4_div_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div4_div_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(io_div4_div_scanmode)
  );

  prim_clock_div #(
    .Divisor(4)
  ) u_no_scan_io_div4_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .step_down_req_i(io_step_down_req),
    .step_down_ack_o(step_down_acks[1]),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(io_div4_div_scanmode[0])),
    .clk_o(clk_io_div4_i)
  );

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  logic [NumAlerts-1:0] alert_test, alerts;
  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  // SEC_CM: MEAS.CONFIG.REGWEN
  // SEC_CM: CLK_CTRL.CONFIG.REGWEN
  clkmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
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
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(hw2reg.fatal_err_code.reg_intg.de),
    .devmode_i(1'b1)
  );
  assign hw2reg.fatal_err_code.reg_intg.d = 1'b1;


  ////////////////////////////////////////////////////
  // Alerts
  ////////////////////////////////////////////////////

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_fault.q & reg2hw.alert_test.recov_fault.qe
  };

  logic recov_alert;
  assign recov_alert =
    hw2reg.recov_err_code.io_update_err.de |
    hw2reg.recov_err_code.io_measure_err.de |
    hw2reg.recov_err_code.io_timeout_err.de |
    hw2reg.recov_err_code.io_div2_update_err.de |
    hw2reg.recov_err_code.io_div2_measure_err.de |
    hw2reg.recov_err_code.io_div2_timeout_err.de |
    hw2reg.recov_err_code.io_div4_update_err.de |
    hw2reg.recov_err_code.io_div4_measure_err.de |
    hw2reg.recov_err_code.io_div4_timeout_err.de |
    hw2reg.recov_err_code.main_update_err.de |
    hw2reg.recov_err_code.main_measure_err.de |
    hw2reg.recov_err_code.main_timeout_err.de |
    hw2reg.recov_err_code.usb_update_err.de |
    hw2reg.recov_err_code.usb_measure_err.de |
    hw2reg.recov_err_code.usb_timeout_err.de;

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

  mubi4_t low_speed_sel;
  assign low_speed_sel = mubi4_t'(reg2hw.extclk_ctrl.low_speed_sel.q);
  clkmgr_byp #(
    .NumDivClks(2)
  ) u_clkmgr_byp (
    .clk_i,
    .rst_ni,
    .en_i(lc_hw_debug_en_i),
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .byp_req_i(mubi4_t'(reg2hw.extclk_ctrl.sel.q)),
    .low_speed_sel_i(low_speed_sel),
    .all_clk_byp_req_o,
    .all_clk_byp_ack_i,
    .io_clk_byp_req_o,
    .io_clk_byp_ack_i,

    // divider step down controls
    .step_down_acks_i(step_down_acks),
    .step_down_req_o(step_down_req)
  );

  // the external consumer of this signal requires the opposite polarity
  prim_flop #(
    .ResetValue(1'b1)
  ) u_high_speed_sel (
    .clk_i,
    .rst_ni,
    .d_i(mubi4_test_false_loose(low_speed_sel)),
    .q_o(hi_speed_sel_o)
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
  // Distribute pwrmgr ip_clk_en requests to each family
  ////////////////////////////////////////////////////
  // clk_main family
  logic pwrmgr_main_en;
  assign pwrmgr_main_en = pwr_i.main_ip_clk_en;

  // clk_io family
  logic pwrmgr_io_en;
  logic pwrmgr_io_div2_en;
  logic pwrmgr_io_div4_en;
  assign pwrmgr_io_en = pwr_i.io_ip_clk_en;
  assign pwrmgr_io_div2_en = pwr_i.io_ip_clk_en;
  assign pwrmgr_io_div4_en = pwr_i.io_ip_clk_en;

  // clk_usb family
  logic pwrmgr_usb_en;
  assign pwrmgr_usb_en = pwr_i.usb_ip_clk_en;


  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  // clk_main family
  logic [0:0] main_ens;

  logic clk_main_en;
  logic clk_main_root;
  clkmgr_root_ctrl u_main_root_ctrl (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_main_en),
    .en_o(clk_main_en),
    .clk_o(clk_main_root)
  );
  assign main_ens[0] = clk_main_en;

  // create synchronized status
  clkmgr_clk_status #(
    .NumClocks(1)
  ) u_main_status (
    .clk_i,
    .rst_ni,
    .ens_i(main_ens),
    .status_o(pwr_o.main_status)
  );

  // clk_io family
  logic [2:0] io_ens;

  logic clk_io_en;
  logic clk_io_root;
  clkmgr_root_ctrl u_io_root_ctrl (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_io_en),
    .en_o(clk_io_en),
    .clk_o(clk_io_root)
  );
  assign io_ens[0] = clk_io_en;

  logic clk_io_div2_en;
  logic clk_io_div2_root;
  clkmgr_root_ctrl u_io_div2_root_ctrl (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_io_div2_en),
    .en_o(clk_io_div2_en),
    .clk_o(clk_io_div2_root)
  );
  assign io_ens[1] = clk_io_div2_en;

  logic clk_io_div4_en;
  logic clk_io_div4_root;
  clkmgr_root_ctrl u_io_div4_root_ctrl (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_io_div4_en),
    .en_o(clk_io_div4_en),
    .clk_o(clk_io_div4_root)
  );
  assign io_ens[2] = clk_io_div4_en;

  // create synchronized status
  clkmgr_clk_status #(
    .NumClocks(3)
  ) u_io_status (
    .clk_i,
    .rst_ni,
    .ens_i(io_ens),
    .status_o(pwr_o.io_status)
  );

  // clk_usb family
  logic [0:0] usb_ens;

  logic clk_usb_en;
  logic clk_usb_root;
  clkmgr_root_ctrl u_usb_root_ctrl (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_usb_en),
    .en_o(clk_usb_en),
    .clk_o(clk_usb_root)
  );
  assign usb_ens[0] = clk_usb_en;

  // create synchronized status
  clkmgr_clk_status #(
    .NumClocks(1)
  ) u_usb_status (
    .clk_i,
    .rst_ni,
    .ens_i(usb_ens),
    .status_o(pwr_o.usb_status)
  );

  ////////////////////////////////////////////////////
  // Clock Measurement for the roots
  // SEC_CM: TIMEOUT.CLK.BKGN_CHK, MEAS.CLK.BKGN_CHK
  ////////////////////////////////////////////////////

  logic io_fast_err;
  logic io_slow_err;
  logic io_timeout_err;
    prim_clock_meas #(
    .Cnt(960),
    .RefCnt(1),
    .ClkTimeOutChkEn(1'b1),
    .RefTimeOutChkEn(1'b0)
  ) u_io_meas (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_io_en & reg2hw.io_meas_ctrl_shadowed.en.q),
    .max_cnt(reg2hw.io_meas_ctrl_shadowed.hi.q),
    .min_cnt(reg2hw.io_meas_ctrl_shadowed.lo.q),
    .valid_o(),
    .fast_o(io_fast_err),
    .slow_o(io_slow_err),
    .timeout_clk_ref_o(),
    .ref_timeout_clk_o(io_timeout_err)
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

  logic synced_io_timeout_err;
  prim_edge_detector #(
    .Width(1),
    .ResetValue('0),
    .EnSync(1'b1)
  ) u_io_timeout_err_sync (
    .clk_i,
    .rst_ni,
    .d_i(io_timeout_err),
    .q_sync_o(),
    .q_posedge_pulse_o(synced_io_timeout_err),
    .q_negedge_pulse_o()
  );

  assign hw2reg.recov_err_code.io_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_measure_err.de = synced_io_err;
  assign hw2reg.recov_err_code.io_timeout_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_timeout_err.de = synced_io_timeout_err;
  assign hw2reg.recov_err_code.io_update_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_update_err.de =
    reg2hw.io_meas_ctrl_shadowed.en.err_update |
    reg2hw.io_meas_ctrl_shadowed.hi.err_update |
    reg2hw.io_meas_ctrl_shadowed.lo.err_update;
  assign hw2reg.fatal_err_code.io_storage_err.d = 1'b1;
  assign hw2reg.fatal_err_code.io_storage_err.de =
    reg2hw.io_meas_ctrl_shadowed.en.err_storage |
    reg2hw.io_meas_ctrl_shadowed.hi.err_storage |
    reg2hw.io_meas_ctrl_shadowed.lo.err_storage;

  logic io_div2_fast_err;
  logic io_div2_slow_err;
  logic io_div2_timeout_err;
    prim_clock_meas #(
    .Cnt(480),
    .RefCnt(1),
    .ClkTimeOutChkEn(1'b1),
    .RefTimeOutChkEn(1'b0)
  ) u_io_div2_meas (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_io_div2_en & reg2hw.io_div2_meas_ctrl_shadowed.en.q),
    .max_cnt(reg2hw.io_div2_meas_ctrl_shadowed.hi.q),
    .min_cnt(reg2hw.io_div2_meas_ctrl_shadowed.lo.q),
    .valid_o(),
    .fast_o(io_div2_fast_err),
    .slow_o(io_div2_slow_err),
    .timeout_clk_ref_o(),
    .ref_timeout_clk_o(io_div2_timeout_err)
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

  logic synced_io_div2_timeout_err;
  prim_edge_detector #(
    .Width(1),
    .ResetValue('0),
    .EnSync(1'b1)
  ) u_io_div2_timeout_err_sync (
    .clk_i,
    .rst_ni,
    .d_i(io_div2_timeout_err),
    .q_sync_o(),
    .q_posedge_pulse_o(synced_io_div2_timeout_err),
    .q_negedge_pulse_o()
  );

  assign hw2reg.recov_err_code.io_div2_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div2_measure_err.de = synced_io_div2_err;
  assign hw2reg.recov_err_code.io_div2_timeout_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div2_timeout_err.de = synced_io_div2_timeout_err;
  assign hw2reg.recov_err_code.io_div2_update_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div2_update_err.de =
    reg2hw.io_div2_meas_ctrl_shadowed.en.err_update |
    reg2hw.io_div2_meas_ctrl_shadowed.hi.err_update |
    reg2hw.io_div2_meas_ctrl_shadowed.lo.err_update;
  assign hw2reg.fatal_err_code.io_div2_storage_err.d = 1'b1;
  assign hw2reg.fatal_err_code.io_div2_storage_err.de =
    reg2hw.io_div2_meas_ctrl_shadowed.en.err_storage |
    reg2hw.io_div2_meas_ctrl_shadowed.hi.err_storage |
    reg2hw.io_div2_meas_ctrl_shadowed.lo.err_storage;

  logic io_div4_fast_err;
  logic io_div4_slow_err;
  logic io_div4_timeout_err;
    prim_clock_meas #(
    .Cnt(240),
    .RefCnt(1),
    .ClkTimeOutChkEn(1'b1),
    .RefTimeOutChkEn(1'b0)
  ) u_io_div4_meas (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_io_div4_en & reg2hw.io_div4_meas_ctrl_shadowed.en.q),
    .max_cnt(reg2hw.io_div4_meas_ctrl_shadowed.hi.q),
    .min_cnt(reg2hw.io_div4_meas_ctrl_shadowed.lo.q),
    .valid_o(),
    .fast_o(io_div4_fast_err),
    .slow_o(io_div4_slow_err),
    .timeout_clk_ref_o(),
    .ref_timeout_clk_o(io_div4_timeout_err)
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

  logic synced_io_div4_timeout_err;
  prim_edge_detector #(
    .Width(1),
    .ResetValue('0),
    .EnSync(1'b1)
  ) u_io_div4_timeout_err_sync (
    .clk_i,
    .rst_ni,
    .d_i(io_div4_timeout_err),
    .q_sync_o(),
    .q_posedge_pulse_o(synced_io_div4_timeout_err),
    .q_negedge_pulse_o()
  );

  assign hw2reg.recov_err_code.io_div4_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div4_measure_err.de = synced_io_div4_err;
  assign hw2reg.recov_err_code.io_div4_timeout_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div4_timeout_err.de = synced_io_div4_timeout_err;
  assign hw2reg.recov_err_code.io_div4_update_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div4_update_err.de =
    reg2hw.io_div4_meas_ctrl_shadowed.en.err_update |
    reg2hw.io_div4_meas_ctrl_shadowed.hi.err_update |
    reg2hw.io_div4_meas_ctrl_shadowed.lo.err_update;
  assign hw2reg.fatal_err_code.io_div4_storage_err.d = 1'b1;
  assign hw2reg.fatal_err_code.io_div4_storage_err.de =
    reg2hw.io_div4_meas_ctrl_shadowed.en.err_storage |
    reg2hw.io_div4_meas_ctrl_shadowed.hi.err_storage |
    reg2hw.io_div4_meas_ctrl_shadowed.lo.err_storage;

  logic main_fast_err;
  logic main_slow_err;
  logic main_timeout_err;
    prim_clock_meas #(
    .Cnt(1000),
    .RefCnt(1),
    .ClkTimeOutChkEn(1'b1),
    .RefTimeOutChkEn(1'b0)
  ) u_main_meas (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_main_en & reg2hw.main_meas_ctrl_shadowed.en.q),
    .max_cnt(reg2hw.main_meas_ctrl_shadowed.hi.q),
    .min_cnt(reg2hw.main_meas_ctrl_shadowed.lo.q),
    .valid_o(),
    .fast_o(main_fast_err),
    .slow_o(main_slow_err),
    .timeout_clk_ref_o(),
    .ref_timeout_clk_o(main_timeout_err)
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

  logic synced_main_timeout_err;
  prim_edge_detector #(
    .Width(1),
    .ResetValue('0),
    .EnSync(1'b1)
  ) u_main_timeout_err_sync (
    .clk_i,
    .rst_ni,
    .d_i(main_timeout_err),
    .q_sync_o(),
    .q_posedge_pulse_o(synced_main_timeout_err),
    .q_negedge_pulse_o()
  );

  assign hw2reg.recov_err_code.main_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.main_measure_err.de = synced_main_err;
  assign hw2reg.recov_err_code.main_timeout_err.d = 1'b1;
  assign hw2reg.recov_err_code.main_timeout_err.de = synced_main_timeout_err;
  assign hw2reg.recov_err_code.main_update_err.d = 1'b1;
  assign hw2reg.recov_err_code.main_update_err.de =
    reg2hw.main_meas_ctrl_shadowed.en.err_update |
    reg2hw.main_meas_ctrl_shadowed.hi.err_update |
    reg2hw.main_meas_ctrl_shadowed.lo.err_update;
  assign hw2reg.fatal_err_code.main_storage_err.d = 1'b1;
  assign hw2reg.fatal_err_code.main_storage_err.de =
    reg2hw.main_meas_ctrl_shadowed.en.err_storage |
    reg2hw.main_meas_ctrl_shadowed.hi.err_storage |
    reg2hw.main_meas_ctrl_shadowed.lo.err_storage;

  logic usb_fast_err;
  logic usb_slow_err;
  logic usb_timeout_err;
    prim_clock_meas #(
    .Cnt(480),
    .RefCnt(1),
    .ClkTimeOutChkEn(1'b1),
    .RefTimeOutChkEn(1'b0)
  ) u_usb_meas (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_usb_en & reg2hw.usb_meas_ctrl_shadowed.en.q),
    .max_cnt(reg2hw.usb_meas_ctrl_shadowed.hi.q),
    .min_cnt(reg2hw.usb_meas_ctrl_shadowed.lo.q),
    .valid_o(),
    .fast_o(usb_fast_err),
    .slow_o(usb_slow_err),
    .timeout_clk_ref_o(),
    .ref_timeout_clk_o(usb_timeout_err)
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

  logic synced_usb_timeout_err;
  prim_edge_detector #(
    .Width(1),
    .ResetValue('0),
    .EnSync(1'b1)
  ) u_usb_timeout_err_sync (
    .clk_i,
    .rst_ni,
    .d_i(usb_timeout_err),
    .q_sync_o(),
    .q_posedge_pulse_o(synced_usb_timeout_err),
    .q_negedge_pulse_o()
  );

  assign hw2reg.recov_err_code.usb_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.usb_measure_err.de = synced_usb_err;
  assign hw2reg.recov_err_code.usb_timeout_err.d = 1'b1;
  assign hw2reg.recov_err_code.usb_timeout_err.de = synced_usb_timeout_err;
  assign hw2reg.recov_err_code.usb_update_err.d = 1'b1;
  assign hw2reg.recov_err_code.usb_update_err.de =
    reg2hw.usb_meas_ctrl_shadowed.en.err_update |
    reg2hw.usb_meas_ctrl_shadowed.hi.err_update |
    reg2hw.usb_meas_ctrl_shadowed.lo.err_update;
  assign hw2reg.fatal_err_code.usb_storage_err.d = 1'b1;
  assign hw2reg.fatal_err_code.usb_storage_err.de =
    reg2hw.usb_meas_ctrl_shadowed.en.err_storage |
    reg2hw.usb_meas_ctrl_shadowed.hi.err_storage |
    reg2hw.usb_meas_ctrl_shadowed.lo.err_storage;


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
  assign clocks_o.clk_io_infra = clk_io_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_infra (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .mubi_i(((clk_io_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_infra)
  );
  assign clocks_o.clk_io_div2_infra = clk_io_div2_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_div2_infra (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .mubi_i(((clk_io_div2_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_div2_infra)
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
  logic clk_usb_peri_sw_en;
  logic clk_io_peri_sw_en;

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_div4_peri_sw_en_sync (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .d_i(reg2hw.clk_enables.clk_io_div4_peri_en.q),
    .q_o(clk_io_div4_peri_sw_en)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_io_div4_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div4_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_div4_peri_scanmode)
  );

  logic clk_io_div4_peri_combined_en;
  assign clk_io_div4_peri_combined_en = clk_io_div4_peri_sw_en & clk_io_div4_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_div4_peri_cg (
    .clk_i(clk_io_div4_root),
    .en_i(clk_io_div4_peri_combined_en),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_io_div4_peri_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_io_div2_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div2_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_div2_peri_scanmode)
  );

  logic clk_io_div2_peri_combined_en;
  assign clk_io_div2_peri_combined_en = clk_io_div2_peri_sw_en & clk_io_div2_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_div2_peri_cg (
    .clk_i(clk_io_div2_root),
    .en_i(clk_io_div2_peri_combined_en),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_io_div2_peri_scanmode[0])),
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
  ) u_clk_usb_peri_sw_en_sync (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .d_i(reg2hw.clk_enables.clk_usb_peri_en.q),
    .q_o(clk_usb_peri_sw_en)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_usb_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_usb_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_usb_peri_scanmode)
  );

  logic clk_usb_peri_combined_en;
  assign clk_usb_peri_combined_en = clk_usb_peri_sw_en & clk_usb_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_usb_peri_cg (
    .clk_i(clk_usb_root),
    .en_i(clk_usb_peri_combined_en),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_usb_peri_scanmode[0])),
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

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_peri_sw_en_sync (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .d_i(reg2hw.clk_enables.clk_io_peri_en.q),
    .q_o(clk_io_peri_sw_en)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_io_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_peri_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_peri_scanmode)
  );

  logic clk_io_peri_combined_en;
  assign clk_io_peri_combined_en = clk_io_peri_sw_en & clk_io_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_peri_cg (
    .clk_i(clk_io_root),
    .en_i(clk_io_peri_combined_en),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_io_peri_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_main_aes_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_aes_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_main_aes_scanmode)
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
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_main_aes_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_main_hmac_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_hmac_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_main_hmac_scanmode)
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
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_main_hmac_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_main_kmac_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_kmac_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_main_kmac_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic clk_main_kmac_combined_en;
  prim_buf u_prim_buf_clk_main_kmac_en (
    .in_i(clk_main_kmac_en & clk_main_en),
    .out_o(clk_main_kmac_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // KMAC is getting too big for a single clock region.
  ) u_clk_main_kmac_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_kmac_combined_en),
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_main_kmac_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_main_otbn_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_main_otbn_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_main_otbn_scanmode)
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
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_main_otbn_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_io_div4_otbn_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div4_otbn_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_div4_otbn_scanmode)
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
    .test_en_i(prim_mubi_pkg::mubi4_test_true_strict(clk_io_div4_otbn_scanmode[0])),
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

  // SEC_CM: JITTER.CONFIG.MUBI
  assign jitter_en_o = mubi4_test_true_loose(mubi4_t'(reg2hw.jitter_enable.q));

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
  `ASSERT_KNOWN(AllClkBypReqKnownO_A, all_clk_byp_req_o)
  `ASSERT_KNOWN(IoClkBypReqKnownO_A, io_clk_byp_req_o)
  `ASSERT_KNOWN(LcCtrlClkBypAckKnownO_A, lc_clk_byp_ack_o)
  `ASSERT_KNOWN(JitterEnableKnownO_A, jitter_en_o)
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)
  `ASSERT_KNOWN(CgEnKnownO_A, cg_en_o)

endmodule // clkmgr
