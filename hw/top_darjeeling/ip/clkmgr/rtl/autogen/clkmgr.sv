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

  // Resets for derived clock generation, root clock gating and related status
  input rst_root_ni,
  input rst_root_main_ni,
  input rst_root_io_ni,
  input rst_root_io_div2_ni,
  input rst_root_io_div4_ni,
  input rst_root_usb_ni,

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
  // SEC_CM: IDLE.INTERSIG.MUBI
  input prim_mubi_pkg::mubi4_t [3:0] idle_i,

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
  output mubi4_t hi_speed_sel_o,

  // clock calibration has been done.
  // If this is signal is 0, assume clock frequencies to be
  // uncalibrated.
  input prim_mubi_pkg::mubi4_t calib_rdy_i,

  // jittery enable to ast
  output mubi4_t jitter_en_o,

  // external indication for whether dividers should be stepped down
  // SEC_CM: DIV.INTERSIG.MUBI
  input mubi4_t div_step_down_req_i,

  // clock gated indications going to alert handlers
  output clkmgr_cg_en_t cg_en_o,

  // clock output interface
  output clkmgr_out_t clocks_o

);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::mubi4_test_false_strict;

  ////////////////////////////////////////////////////
  // External step down request
  ////////////////////////////////////////////////////
  mubi4_t io_step_down_req;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(1),
    .StabilityCheck(1),
    .ResetValue(MuBi4False)
  ) u_io_step_down_req_sync (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .mubi_i(div_step_down_req_i),
    .mubi_o({io_step_down_req})
  );


  ////////////////////////////////////////////////////
  // Divided clocks
  // Note divided clocks must use the por version of
  // its related reset to ensure clock division
  // can happen without any dependency
  ////////////////////////////////////////////////////

  logic [1:0] step_down_acks;

  logic clk_io_div2_i;
  logic clk_io_div4_i;


  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] io_div2_div_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div2_div_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o({io_div2_div_scanmode})
  );

  prim_clock_div #(
    .Divisor(2)
  ) u_no_scan_io_div2_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_root_io_ni),
    .step_down_req_i(mubi4_test_true_strict(io_step_down_req)),
    .step_down_ack_o(step_down_acks[0]),
    .test_en_i(mubi4_test_true_strict(io_div2_div_scanmode[0])),
    .clk_o(clk_io_div2_i)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] io_div4_div_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_io_div4_div_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o({io_div4_div_scanmode})
  );

  prim_clock_div #(
    .Divisor(4)
  ) u_no_scan_io_div4_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_root_io_ni),
    .step_down_req_i(mubi4_test_true_strict(io_step_down_req)),
    .step_down_ack_o(step_down_acks[1]),
    .test_en_i(mubi4_test_true_strict(io_div4_div_scanmode[0])),
    .clk_o(clk_io_div4_i)
  );

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  logic [NumAlerts-1:0] alert_test, alerts;
  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  // SEC_CM: MEAS.CONFIG.REGWEN
  // SEC_CM: MEAS.CONFIG.SHADOW
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
    .shadowed_storage_err_o(hw2reg.fatal_err_code.shadow_storage_err.de),
    .shadowed_update_err_o(hw2reg.recov_err_code.shadow_update_err.de),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(hw2reg.fatal_err_code.reg_intg.de),
    .devmode_i(1'b1)
  );
  assign hw2reg.fatal_err_code.reg_intg.d = 1'b1;
  assign hw2reg.recov_err_code.shadow_update_err.d = 1'b1;
  assign hw2reg.fatal_err_code.shadow_storage_err.d = 1'b1;

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
    hw2reg.recov_err_code.io_timeout_err.de |
    hw2reg.recov_err_code.io_div2_measure_err.de |
    hw2reg.recov_err_code.io_div2_timeout_err.de |
    hw2reg.recov_err_code.io_div4_measure_err.de |
    hw2reg.recov_err_code.io_div4_timeout_err.de |
    hw2reg.recov_err_code.main_measure_err.de |
    hw2reg.recov_err_code.main_timeout_err.de |
    hw2reg.recov_err_code.usb_measure_err.de |
    hw2reg.recov_err_code.usb_timeout_err.de |
    hw2reg.recov_err_code.shadow_update_err.de;

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

  mubi4_t extclk_ctrl_sel;
  mubi4_t extclk_ctrl_hi_speed_sel;

  assign extclk_ctrl_sel = mubi4_t'(reg2hw.extclk_ctrl.sel.q);
  assign extclk_ctrl_hi_speed_sel = mubi4_t'(reg2hw.extclk_ctrl.hi_speed_sel.q);

  clkmgr_byp #(
    .NumDivClks(2)
  ) u_clkmgr_byp (
    .clk_i,
    .rst_ni,
    .en_i(lc_hw_debug_en_i),
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .byp_req_i(extclk_ctrl_sel),
    .byp_ack_o(hw2reg.extclk_status.d),
    .hi_speed_sel_i(extclk_ctrl_hi_speed_sel),
    .all_clk_byp_req_o,
    .all_clk_byp_ack_i,
    .io_clk_byp_req_o,
    .io_clk_byp_ack_i,
    .hi_speed_sel_o,

    // divider step down controls
    .step_down_acks_i(step_down_acks)
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
    .rst_ni(rst_root_main_ni),
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
    .rst_ni(rst_root_ni),
    .ens_i(main_ens),
    .status_o(pwr_o.main_status)
  );

  // clk_io family
  logic [2:0] io_ens;

  logic clk_io_en;
  logic clk_io_root;
  clkmgr_root_ctrl u_io_root_ctrl (
    .clk_i(clk_io_i),
    .rst_ni(rst_root_io_ni),
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
    .rst_ni(rst_root_io_div2_ni),
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
    .rst_ni(rst_root_io_div4_ni),
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
    .rst_ni(rst_root_ni),
    .ens_i(io_ens),
    .status_o(pwr_o.io_status)
  );

  // clk_usb family
  logic [0:0] usb_ens;

  logic clk_usb_en;
  logic clk_usb_root;
  clkmgr_root_ctrl u_usb_root_ctrl (
    .clk_i(clk_usb_i),
    .rst_ni(rst_root_usb_ni),
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
    .rst_ni(rst_root_ni),
    .ens_i(usb_ens),
    .status_o(pwr_o.usb_status)
  );

  ////////////////////////////////////////////////////
  // Clock Measurement for the roots
  // SEC_CM: TIMEOUT.CLK.BKGN_CHK, MEAS.CLK.BKGN_CHK
  ////////////////////////////////////////////////////

  typedef enum logic [2:0] {
    BaseIdx,
    ClkIoIdx,
    ClkIoDiv2Idx,
    ClkIoDiv4Idx,
    ClkMainIdx,
    ClkUsbIdx,
    CalibRdyLastIdx
  } clkmgr_calib_idx_e;

  // if clocks become uncalibrated, allow the measurement control configurations to change
  mubi4_t [CalibRdyLastIdx-1:0] calib_rdy;
  prim_mubi4_sync #(
    .AsyncOn(1),
    .NumCopies(int'(CalibRdyLastIdx)),
    .ResetValue(MuBi4False)
  ) u_calib_rdy_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(calib_rdy_i),
    .mubi_o({calib_rdy})
  );

  always_comb begin
    hw2reg.measure_ctrl_regwen.de = '0;
    hw2reg.measure_ctrl_regwen.d = reg2hw.measure_ctrl_regwen;

    if (mubi4_test_false_strict(calib_rdy[BaseIdx])) begin
      hw2reg.measure_ctrl_regwen.de = 1'b1;
      hw2reg.measure_ctrl_regwen.d = 1'b1;
    end
  end

  clkmgr_meas_chk #(
    .Cnt(960),
    .RefCnt(1)
  ) u_io_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_io_i),
    .rst_src_ni(rst_io_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    // signals on source domain
    .src_en_i(clk_io_en & mubi4_test_true_loose(mubi4_t'(reg2hw.io_meas_ctrl_en))),
    .src_max_cnt_i(reg2hw.io_meas_ctrl_shadowed.hi.q),
    .src_min_cnt_i(reg2hw.io_meas_ctrl_shadowed.lo.q),
    .src_cfg_meas_en_i(mubi4_t'(reg2hw.io_meas_ctrl_en.q)),
    .src_cfg_meas_en_valid_o(hw2reg.io_meas_ctrl_en.de),
    .src_cfg_meas_en_o(hw2reg.io_meas_ctrl_en.d),
    // signals on local clock domain
    .calib_rdy_i(calib_rdy[ClkIoIdx]),
    .meas_err_o(hw2reg.recov_err_code.io_measure_err.de),
    .timeout_err_o(hw2reg.recov_err_code.io_timeout_err.de)
  );

  assign hw2reg.recov_err_code.io_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_timeout_err.d = 1'b1;


  clkmgr_meas_chk #(
    .Cnt(480),
    .RefCnt(1)
  ) u_io_div2_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_io_div2_i),
    .rst_src_ni(rst_io_div2_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    // signals on source domain
    .src_en_i(clk_io_div2_en & mubi4_test_true_loose(mubi4_t'(reg2hw.io_div2_meas_ctrl_en))),
    .src_max_cnt_i(reg2hw.io_div2_meas_ctrl_shadowed.hi.q),
    .src_min_cnt_i(reg2hw.io_div2_meas_ctrl_shadowed.lo.q),
    .src_cfg_meas_en_i(mubi4_t'(reg2hw.io_div2_meas_ctrl_en.q)),
    .src_cfg_meas_en_valid_o(hw2reg.io_div2_meas_ctrl_en.de),
    .src_cfg_meas_en_o(hw2reg.io_div2_meas_ctrl_en.d),
    // signals on local clock domain
    .calib_rdy_i(calib_rdy[ClkIoDiv2Idx]),
    .meas_err_o(hw2reg.recov_err_code.io_div2_measure_err.de),
    .timeout_err_o(hw2reg.recov_err_code.io_div2_timeout_err.de)
  );

  assign hw2reg.recov_err_code.io_div2_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div2_timeout_err.d = 1'b1;


  clkmgr_meas_chk #(
    .Cnt(240),
    .RefCnt(1)
  ) u_io_div4_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_io_div4_i),
    .rst_src_ni(rst_io_div4_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    // signals on source domain
    .src_en_i(clk_io_div4_en & mubi4_test_true_loose(mubi4_t'(reg2hw.io_div4_meas_ctrl_en))),
    .src_max_cnt_i(reg2hw.io_div4_meas_ctrl_shadowed.hi.q),
    .src_min_cnt_i(reg2hw.io_div4_meas_ctrl_shadowed.lo.q),
    .src_cfg_meas_en_i(mubi4_t'(reg2hw.io_div4_meas_ctrl_en.q)),
    .src_cfg_meas_en_valid_o(hw2reg.io_div4_meas_ctrl_en.de),
    .src_cfg_meas_en_o(hw2reg.io_div4_meas_ctrl_en.d),
    // signals on local clock domain
    .calib_rdy_i(calib_rdy[ClkIoDiv4Idx]),
    .meas_err_o(hw2reg.recov_err_code.io_div4_measure_err.de),
    .timeout_err_o(hw2reg.recov_err_code.io_div4_timeout_err.de)
  );

  assign hw2reg.recov_err_code.io_div4_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.io_div4_timeout_err.d = 1'b1;


  clkmgr_meas_chk #(
    .Cnt(1000),
    .RefCnt(1)
  ) u_main_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_main_i),
    .rst_src_ni(rst_main_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    // signals on source domain
    .src_en_i(clk_main_en & mubi4_test_true_loose(mubi4_t'(reg2hw.main_meas_ctrl_en))),
    .src_max_cnt_i(reg2hw.main_meas_ctrl_shadowed.hi.q),
    .src_min_cnt_i(reg2hw.main_meas_ctrl_shadowed.lo.q),
    .src_cfg_meas_en_i(mubi4_t'(reg2hw.main_meas_ctrl_en.q)),
    .src_cfg_meas_en_valid_o(hw2reg.main_meas_ctrl_en.de),
    .src_cfg_meas_en_o(hw2reg.main_meas_ctrl_en.d),
    // signals on local clock domain
    .calib_rdy_i(calib_rdy[ClkMainIdx]),
    .meas_err_o(hw2reg.recov_err_code.main_measure_err.de),
    .timeout_err_o(hw2reg.recov_err_code.main_timeout_err.de)
  );

  assign hw2reg.recov_err_code.main_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.main_timeout_err.d = 1'b1;


  clkmgr_meas_chk #(
    .Cnt(480),
    .RefCnt(1)
  ) u_usb_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_usb_i),
    .rst_src_ni(rst_usb_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    // signals on source domain
    .src_en_i(clk_usb_en & mubi4_test_true_loose(mubi4_t'(reg2hw.usb_meas_ctrl_en))),
    .src_max_cnt_i(reg2hw.usb_meas_ctrl_shadowed.hi.q),
    .src_min_cnt_i(reg2hw.usb_meas_ctrl_shadowed.lo.q),
    .src_cfg_meas_en_i(mubi4_t'(reg2hw.usb_meas_ctrl_en.q)),
    .src_cfg_meas_en_valid_o(hw2reg.usb_meas_ctrl_en.de),
    .src_cfg_meas_en_o(hw2reg.usb_meas_ctrl_en.d),
    // signals on local clock domain
    .calib_rdy_i(calib_rdy[ClkUsbIdx]),
    .meas_err_o(hw2reg.recov_err_code.usb_measure_err.de),
    .timeout_err_o(hw2reg.recov_err_code.usb_timeout_err.de)
  );

  assign hw2reg.recov_err_code.usb_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.usb_timeout_err.d = 1'b1;


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
  assign clocks_o.clk_usb_infra = clk_usb_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_usb_infra (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .mubi_i(((clk_usb_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.usb_infra)
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_io_div4_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_div4_peri_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_div4_peri_scanmode)
  );

  logic clk_io_div4_peri_combined_en;
  assign clk_io_div4_peri_combined_en = clk_io_div4_peri_sw_en & clk_io_div4_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_div4_peri_cg (
    .clk_i(clk_io_div4_i),
    .en_i(clk_io_div4_peri_combined_en),
    .test_en_i(mubi4_test_true_strict(clk_io_div4_peri_scanmode[0])),
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
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_div2_peri_scanmode)
  );

  logic clk_io_div2_peri_combined_en;
  assign clk_io_div2_peri_combined_en = clk_io_div2_peri_sw_en & clk_io_div2_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_div2_peri_cg (
    .clk_i(clk_io_div2_i),
    .en_i(clk_io_div2_peri_combined_en),
    .test_en_i(mubi4_test_true_strict(clk_io_div2_peri_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_io_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_io_peri_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(clk_io_peri_scanmode)
  );

  logic clk_io_peri_combined_en;
  assign clk_io_peri_combined_en = clk_io_peri_sw_en & clk_io_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_io_peri_cg (
    .clk_i(clk_io_i),
    .en_i(clk_io_peri_combined_en),
    .test_en_i(mubi4_test_true_strict(clk_io_peri_scanmode[0])),
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

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] clk_usb_peri_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_clk_usb_peri_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(clk_usb_peri_scanmode)
  );

  logic clk_usb_peri_combined_en;
  assign clk_usb_peri_combined_en = clk_usb_peri_sw_en & clk_usb_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_clk_usb_peri_cg (
    .clk_i(clk_usb_i),
    .en_i(clk_usb_peri_combined_en),
    .test_en_i(mubi4_test_true_strict(clk_usb_peri_scanmode[0])),
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

  logic [3:0] idle_cnt_err;

  clkmgr_trans #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_aes_trans (
    .clk_i(clk_main_i),
    .clk_gated_i(clk_main_root),
    .rst_ni(rst_main_ni),
    .en_i(clk_main_en),
    .idle_i(idle_i[HintMainAes]),
    .sw_hint_i(reg2hw.clk_hints.clk_main_aes_hint.q),
    .scanmode_i,
    .alert_cg_en_o(cg_en_o.main_aes),
    .clk_o(clocks_o.clk_main_aes),
    .clk_reg_i(clk_i),
    .rst_reg_ni(rst_ni),
    .reg_en_o(hw2reg.clk_hints_status.clk_main_aes_val.d),
    .reg_cnt_err_o(idle_cnt_err[HintMainAes])
  );
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(
    ClkMainAesCountCheck_A,
    u_clk_main_aes_trans.u_idle_cnt,
    alert_tx_o[1])

  clkmgr_trans #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_hmac_trans (
    .clk_i(clk_main_i),
    .clk_gated_i(clk_main_root),
    .rst_ni(rst_main_ni),
    .en_i(clk_main_en),
    .idle_i(idle_i[HintMainHmac]),
    .sw_hint_i(reg2hw.clk_hints.clk_main_hmac_hint.q),
    .scanmode_i,
    .alert_cg_en_o(cg_en_o.main_hmac),
    .clk_o(clocks_o.clk_main_hmac),
    .clk_reg_i(clk_i),
    .rst_reg_ni(rst_ni),
    .reg_en_o(hw2reg.clk_hints_status.clk_main_hmac_val.d),
    .reg_cnt_err_o(idle_cnt_err[HintMainHmac])
  );
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(
    ClkMainHmacCountCheck_A,
    u_clk_main_hmac_trans.u_idle_cnt,
    alert_tx_o[1])

  clkmgr_trans #(
    .FpgaBufGlobal(1'b1) // KMAC is getting too big for a single clock region.
  ) u_clk_main_kmac_trans (
    .clk_i(clk_main_i),
    .clk_gated_i(clk_main_root),
    .rst_ni(rst_main_ni),
    .en_i(clk_main_en),
    .idle_i(idle_i[HintMainKmac]),
    .sw_hint_i(reg2hw.clk_hints.clk_main_kmac_hint.q),
    .scanmode_i,
    .alert_cg_en_o(cg_en_o.main_kmac),
    .clk_o(clocks_o.clk_main_kmac),
    .clk_reg_i(clk_i),
    .rst_reg_ni(rst_ni),
    .reg_en_o(hw2reg.clk_hints_status.clk_main_kmac_val.d),
    .reg_cnt_err_o(idle_cnt_err[HintMainKmac])
  );
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(
    ClkMainKmacCountCheck_A,
    u_clk_main_kmac_trans.u_idle_cnt,
    alert_tx_o[1])

  clkmgr_trans #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_clk_main_otbn_trans (
    .clk_i(clk_main_i),
    .clk_gated_i(clk_main_root),
    .rst_ni(rst_main_ni),
    .en_i(clk_main_en),
    .idle_i(idle_i[HintMainOtbn]),
    .sw_hint_i(reg2hw.clk_hints.clk_main_otbn_hint.q),
    .scanmode_i,
    .alert_cg_en_o(cg_en_o.main_otbn),
    .clk_o(clocks_o.clk_main_otbn),
    .clk_reg_i(clk_i),
    .rst_reg_ni(rst_ni),
    .reg_en_o(hw2reg.clk_hints_status.clk_main_otbn_val.d),
    .reg_cnt_err_o(idle_cnt_err[HintMainOtbn])
  );
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(
    ClkMainOtbnCountCheck_A,
    u_clk_main_otbn_trans.u_idle_cnt,
    alert_tx_o[1])
  assign hw2reg.fatal_err_code.idle_cnt.d = 1'b1;
  assign hw2reg.fatal_err_code.idle_cnt.de = |idle_cnt_err;

  // state readback
  assign hw2reg.clk_hints_status.clk_main_aes_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_kmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.de = 1'b1;

  // SEC_CM: JITTER.CONFIG.MUBI
  assign jitter_en_o = mubi4_t'(reg2hw.jitter_enable.q);

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

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[1])
endmodule // clkmgr
