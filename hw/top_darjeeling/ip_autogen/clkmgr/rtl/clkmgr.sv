// Copyright lowRISC contributors (OpenTitan project).
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
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Number of cycles a differential skew is tolerated on the alert signal
  parameter int unsigned AlertSkewCycles = 1
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
  input clk_aon_i,
  input rst_aon_ni,

  // Resets for derived clocks
  // clocks are derived locally

  // Resets for derived clock generation, root clock gating and related status
  input rst_root_ni,
  input rst_root_main_ni,
  input rst_root_io_ni,

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

  // jittery enable to ast
  output mubi4_t jitter_en_o,

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

  // Hookup point for OCC's on root clocks.
  logic clk_main;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_clk_main_buf (
    .clk_i(clk_main_i),
    .clk_o(clk_main)
  );
  logic clk_io;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_clk_io_buf (
    .clk_i(clk_io_i),
    .clk_o(clk_io)
  );
  logic clk_aon;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_clk_aon_buf (
    .clk_i(clk_aon_i),
    .clk_o(clk_aon)
  );

  ////////////////////////////////////////////////////
  // External step down request
  ////////////////////////////////////////////////////


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
    .clk_io_i(clk_io),
    .rst_io_ni,
    .clk_main_i(clk_main),
    .rst_main_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .shadowed_storage_err_o(hw2reg.fatal_err_code.shadow_storage_err.de),
    .shadowed_update_err_o(hw2reg.recov_err_code.shadow_update_err.de),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(hw2reg.fatal_err_code.reg_intg.de)
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
    hw2reg.recov_err_code.main_measure_err.de |
    hw2reg.recov_err_code.main_timeout_err.de |
    hw2reg.recov_err_code.shadow_update_err.de;

  assign alerts = {
    |reg2hw.fatal_err_code,
    recov_alert
  };

  localparam logic [NumAlerts-1:0] AlertFatal = {1'b1, 1'b0};

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
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
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
  prim_clock_buf u_clk_io_powerup_buf (
    .clk_i(clk_io),
    .clk_o(clocks_o.clk_io_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.io_powerup = MuBi4False;
  prim_clock_buf u_clk_aon_powerup_buf (
    .clk_i(clk_aon),
    .clk_o(clocks_o.clk_aon_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_powerup = MuBi4False;
  prim_clock_buf u_clk_main_powerup_buf (
    .clk_i(clk_main),
    .clk_o(clocks_o.clk_main_powerup)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.main_powerup = MuBi4False;
  prim_clock_buf u_clk_aon_infra_buf (
    .clk_i(clk_aon),
    .clk_o(clocks_o.clk_aon_infra)
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.aon_infra = MuBi4False;
  prim_clock_buf u_clk_aon_timers_buf (
    .clk_i(clk_aon),
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
  assign pwrmgr_io_en = pwr_i.io_ip_clk_en;

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  // clk_main family
  logic [0:0] main_ens;

  logic clk_main_en;
  logic clk_main_root;
  clkmgr_root_ctrl u_main_root_ctrl (
    .clk_i(clk_main),
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
  logic [0:0] io_ens;

  logic clk_io_en;
  logic clk_io_root;
  clkmgr_root_ctrl u_io_root_ctrl (
    .clk_i(clk_io),
    .rst_ni(rst_root_io_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_io_en),
    .en_o(clk_io_en),
    .clk_o(clk_io_root)
  );
  assign io_ens[0] = clk_io_en;

  // create synchronized status
  clkmgr_clk_status #(
    .NumClocks(1)
  ) u_io_status (
    .clk_i,
    .rst_ni(rst_root_ni),
    .ens_i(io_ens),
    .status_o(pwr_o.io_status)
  );

  ////////////////////////////////////////////////////
  // Clock Measurement for the roots
  // SEC_CM: TIMEOUT.CLK.BKGN_CHK, MEAS.CLK.BKGN_CHK
  ////////////////////////////////////////////////////

  typedef enum logic [1:0] {
    BaseIdx,
    ClkIoIdx,
    ClkMainIdx,
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
    .mubi_i(MuBi4False),
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
    .Cnt(512),
    .RefCnt(32)
  ) u_io_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_io),
    .rst_src_ni(rst_io_ni),
    .clk_ref_i(clk_aon),
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
    .Cnt(512),
    .RefCnt(8)
  ) u_main_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_main),
    .rst_src_ni(rst_main_ni),
    .clk_ref_i(clk_aon),
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


  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
  assign clocks_o.clk_io_infra = clk_io_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_infra (
    .clk_i(clk_io),
    .rst_ni(rst_io_ni),
    .mubi_i(((clk_io_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_infra)
  );
  assign clocks_o.clk_main_infra = clk_main_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_infra (
    .clk_i(clk_main),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_infra)
  );
  assign clocks_o.clk_io_secure = clk_io_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_secure (
    .clk_i(clk_io),
    .rst_ni(rst_io_ni),
    .mubi_i(((clk_io_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_secure)
  );
  assign clocks_o.clk_main_secure = clk_main_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_main_secure (
    .clk_i(clk_main),
    .rst_ni(rst_main_ni),
    .mubi_i(((clk_main_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.main_secure)
  );
  assign clocks_o.clk_io_timers = clk_io_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_timers (
    .clk_i(clk_io),
    .rst_ni(rst_io_ni),
    .mubi_i(((clk_io_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_timers)
  );

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

  logic clk_io_peri_sw_en;

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_peri_sw_en_sync (
    .clk_i(clk_io),
    .rst_ni(rst_io_ni),
    .d_i(reg2hw.clk_enables.q),
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
    .clk_i(clk_io),
    .en_i(clk_io_peri_combined_en),
    .test_en_i(mubi4_test_true_strict(clk_io_peri_scanmode[0])),
    .clk_o(clocks_o.clk_io_peri)
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_clk_io_peri (
    .clk_i(clk_io),
    .rst_ni(rst_io_ni),
    .mubi_i(((clk_io_peri_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.io_peri)
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
    .clk_i(clk_main),
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
    .clk_i(clk_main),
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
    .clk_i(clk_main),
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
    .clk_i(clk_main),
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
  `ASSERT_KNOWN(JitterEnableKnownO_A, jitter_en_o)
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)
  `ASSERT_KNOWN(CgEnKnownO_A, cg_en_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[1])
endmodule // clkmgr
