// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primary partition of the split reset manager.
//
// The primary partition hosts:
//  - the register file and the alerts. RESET_REQ, RESET_INFO, ALERT_REGWEN, ALERT_INFO_CTRL,
//    CPU_REGWEN, CPU_INFO_CTRL and ERR_CODE are external, and the secondary partition keeps their
//    state.
//  - the storage of the crash dumps (ALERT_INFO and CPU_INFO). The secondary partition decides
//    the captures.
//  - the leaf resets that the secondary partition does not host.

`include "prim_assert.sv"


module rstmgr_part_primary
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Number of cycles a differential skew is tolerated on the alert signal
  parameter int unsigned AlertSkewCycles = 1,
  parameter bit SecCheck = 1,
  parameter int SecMaxSyncDelay = 2
) (
  // Primary module clocks
  input clk_i,
  input rst_ni,
  input clk_aon_i,
  input clk_io_i,
  input clk_main_i,
  // These ports are the POR clock and the POR reset. The crash dump and its sync registers use
  // them, so that the capture and its enable use the same clock, and an escalation's reset does not
  // clear them. Every clock except the always-on clock enters here. Thus the secondary partition
  // also gets the POR clock from here, for its reset controllers and RESET_INFO.
  input clk_por_i,
  input rst_por_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interface to alert handler
  input alert_handler_pkg::alert_crashdump_t alert_dump_i,

  // Interface to cpu crash dump
  input rv_core_ibex_pkg::cpu_crash_dump_t cpu_dump_i,

  // Reset asserted indications going to alert handler
  output rstmgr_rst_en_primary_t rst_en_o,

  // reset outputs
  output rstmgr_out_primary_t resets_o,

  // inter-partition signalling
  input intraip_s2p_t intraip_s2p_i,
  output intraip_p2s_t intraip_p2s_o
);

  // The scan signals enter only the secondary partition. This partition takes them from
  // intraip_s2p_i. The scan reset gets a net of its own, the same as the roots, so that the
  // crossing struct carries only data where this partition uses it directly.
  logic scan_rst_n;
  assign scan_rst_n = intraip_s2p_i.scan_rst_n;

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  // The crash dump and its registers use the POR clock and the POR reset. Thus an escalation's
  // reset does not clear the crash dump, and software can read it after the escalation. This POR is
  // the POR of the power domain that powers down, so a deep sleep resets them.
  logic clk_por;
  logic rst_por_n;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_clk_buf (
    .clk_i(clk_por_i),
    .clk_o(clk_por)
  );

  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_rst_buf (
    .clk_i(rst_por_ni),
    .clk_o(rst_por_n)
  );


  ////////////////////////////////////////////////////
  // Register Interface                             //
  ////////////////////////////////////////////////////

  rstmgr_reg_pkg::rstmgr_reg2hw_t reg2hw;
  rstmgr_reg_pkg::rstmgr_hw2reg_t hw2reg;

  logic reg_intg_err;
  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: SW_RST.CONFIG.REGWEN, DUMP_CTRL.CONFIG.REGWEN
  rstmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(reg_intg_err)
  );


  ////////////////////////////////////////////////////
  // Errors                                         //
  ////////////////////////////////////////////////////

  // consistency check errors
  logic [10:0] cnsty_chk_errs;
  logic [10:0] fsm_errs;

  // ERR_CODE is external, so the register file keeps no state for it. The errors of this partition
  // go to the secondary partition, which keeps the record of all of them in the always-on power
  // domain. ERR_CODE and the alerts read that record.
  assign intraip_p2s_o.reg_intg_err  = reg_intg_err;
  // The clocks that the secondary partition uses, which enter this partition only.
  assign intraip_p2s_o.clk     = clk_i;
  assign intraip_p2s_o.clk_por = clk_por_i;
  assign intraip_p2s_o.clk_io  = clk_io_i;
  assign intraip_p2s_o.cnsty_chk_err = |cnsty_chk_errs;
  assign intraip_p2s_o.fsm_err       = |fsm_errs;

  assign hw2reg.err_code.reg_intg_err.d          = intraip_s2p_i.reg_intg_err_q;
  assign hw2reg.err_code.reset_consistency_err.d = intraip_s2p_i.cnsty_chk_err_q;
  assign hw2reg.err_code.fsm_err.d               = intraip_s2p_i.fsm_err_q;
  ////////////////////////////////////////////////////
  // Alerts                                         //
  ////////////////////////////////////////////////////
  logic [NumAlerts-1:0] alert_test, alerts;

  // All of these are fatal alerts
  assign alerts[0] = intraip_s2p_i.reg_intg_err_q | intraip_s2p_i.fsm_err_q;

  assign alerts[1] = intraip_s2p_i.cnsty_chk_err_q;

  assign alert_test = {
    reg2hw.alert_test.fatal_cnsty_fault.q & reg2hw.alert_test.fatal_cnsty_fault.qe,
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
      .IsFatal(1'b1)
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
  // Source resets in the system                    //
  ////////////////////////////////////////////////////

  // The secondary partition generates the root resets, which are the POR root and the lc and sys
  // sources of each power domain. This partition receives the roots that its leaves use, in
  // intraip_s2p_i.
  //  - rst_por_aon_n_main
  //  - rst_lc_src_n_main
  //  - rst_sys_src_n_main


  ////////////////////////////////////////////////////
  // leaf reset in the system                       //
  // These should all be generated                  //
  ////////////////////////////////////////////////////
  // Each leaf generates only the variants that this partition hosts. Nothing is tied off.

  // The roots that the leaves here have as parents come from the secondary partition. Each root
  // gets a local net, so a leaf connects to a plain signal rather than to a field of intraip_s2p_i.
  // A force on the parent reset of a leaf in the DV then reaches an ordinary net.
  logic rst_por_aon_n_main;
  assign rst_por_aon_n_main = intraip_s2p_i.rst_por_aon_n_main;
  logic rst_lc_src_n_main;
  assign rst_lc_src_n_main = intraip_s2p_i.rst_lc_src_n_main;
  logic rst_sys_src_n_main;
  assign rst_sys_src_n_main = intraip_s2p_i.rst_sys_src_n_main;

  // Generating resets for por
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_por (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_main_i),
    .parent_rst_ni(rst_por_aon_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.por),
    .leaf_rst_o(resets_o.rst_por_n),
    .err_o(cnsty_chk_errs[0]),
    .fsm_err_o(fsm_errs[0])
  );
  if (SecCheck) begin : gen_dmain_por_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainPorFsmCheck_A,
    u_dmain_por.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for por_io
  // Power Domains: ['Aon', 'Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_por_io (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_por_aon_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.por_io[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_por_io_n),
    .err_o(cnsty_chk_errs[1]),
    .fsm_err_o(fsm_errs[1])
  );
  if (SecCheck) begin : gen_dmain_por_io_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainPorIoFsmCheck_A,
    u_dmain_por_io.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for lc
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: True
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_main_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc),
    .leaf_rst_o(resets_o.rst_lc_n),
    .err_o(cnsty_chk_errs[2]),
    .fsm_err_o(fsm_errs[2])
  );
  if (SecCheck) begin : gen_dmain_lc_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainLcFsmCheck_A,
    u_dmain_lc.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_shadowed (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_main_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_shadowed),
    .leaf_rst_o(resets_o.rst_lc_shadowed_n),
    .err_o(cnsty_chk_errs[3]),
    .fsm_err_o(fsm_errs[3])
  );
  if (SecCheck) begin : gen_dmain_lc_shadowed_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainLcShadowedFsmCheck_A,
    u_dmain_lc_shadowed.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for lc_aon
  // Power Domains: ['Main', 'Aon'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_aon (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_aon_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_aon[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_lc_aon_n),
    .err_o(cnsty_chk_errs[4]),
    .fsm_err_o(fsm_errs[4])
  );
  if (SecCheck) begin : gen_dmain_lc_aon_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainLcAonFsmCheck_A,
    u_dmain_lc_aon.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for lc_io
  // Power Domains: ['Main', 'Aon'], hosted in this partition: ['Main']
  // Shadowed: True
  rstmgr_leaf_rst #(
    .SecCheck(0),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_io (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_io[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_lc_io_n),
    .err_o(cnsty_chk_errs[5]),
    .fsm_err_o(fsm_errs[5])
  );
  rstmgr_leaf_rst #(
    .SecCheck(0),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_io_shadowed (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_io_shadowed[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_lc_io_shadowed_n),
    .err_o(cnsty_chk_errs[6]),
    .fsm_err_o(fsm_errs[6])
  );
  // Generating resets for sys
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_sys (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_main_i),
    .parent_rst_ni(rst_sys_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.sys),
    .leaf_rst_o(resets_o.rst_sys_n),
    .err_o(cnsty_chk_errs[7]),
    .fsm_err_o(fsm_errs[7])
  );
  if (SecCheck) begin : gen_dmain_sys_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainSysFsmCheck_A,
    u_dmain_sys.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for spi_device
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_spi_device (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[SPI_DEVICE].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.spi_device),
    .leaf_rst_o(resets_o.rst_spi_device_n),
    .err_o(cnsty_chk_errs[8]),
    .fsm_err_o(fsm_errs[8])
  );
  if (SecCheck) begin : gen_dmain_spi_device_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainSpiDeviceFsmCheck_A,
    u_dmain_spi_device.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for spi_host0
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_spi_host0 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[SPI_HOST0].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.spi_host0),
    .leaf_rst_o(resets_o.rst_spi_host0_n),
    .err_o(cnsty_chk_errs[9]),
    .fsm_err_o(fsm_errs[9])
  );
  if (SecCheck) begin : gen_dmain_spi_host0_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainSpiHost0FsmCheck_A,
    u_dmain_spi_host0.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for i2c0
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_i2c0 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[I2C0].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.i2c0),
    .leaf_rst_o(resets_o.rst_i2c0_n),
    .err_o(cnsty_chk_errs[10]),
    .fsm_err_o(fsm_errs[10])
  );
  if (SecCheck) begin : gen_dmain_i2c0_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainI2c0FsmCheck_A,
    u_dmain_i2c0.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end

  ////////////////////////////////////////////////////
  // Reset info construction                        //
  ////////////////////////////////////////////////////

  // RESET_REQ is external (hwext). The secondary partition keeps the software reset request in
  // the always-on power domain, and sends it to the power manager. This partition reads it, and
  // forwards the software writes.
  assign hw2reg.reset_req.d         = intraip_s2p_i.reset_req_q;
  assign intraip_p2s_o.reset_req_we = reg2hw.reset_req.qe;
  assign intraip_p2s_o.reset_req_wd = prim_mubi_pkg::mubi4_t'(reg2hw.reset_req.q);

  // RESET_INFO is external (hwext). The secondary partition keeps the reset reasons in the
  // always-on power domain, so that they survive a deep sleep. This partition reads them. It
  // decodes the software writes into one clear per bit (rw1c), and forwards them.
  assign hw2reg.reset_info = intraip_s2p_i.reset_info_q;
  assign intraip_p2s_o.por_clr =
      reg2hw.reset_info.por.qe & reg2hw.reset_info.por.q;
  assign intraip_p2s_o.low_power_exit_clr =
      reg2hw.reset_info.low_power_exit.qe & reg2hw.reset_info.low_power_exit.q;
  assign intraip_p2s_o.sw_reset_clr =
      reg2hw.reset_info.sw_reset.qe & reg2hw.reset_info.sw_reset.q;
  assign intraip_p2s_o.hw_req_clr =
      {rstmgr_reg_pkg::NumHwResets{reg2hw.reset_info.hw_req.qe}} & reg2hw.reset_info.hw_req.q;

  ////////////////////////////////////////////////////
  // Crash info capture                             //
  ////////////////////////////////////////////////////

  // The secondary partition decides the captures: a hardware reset or a low power entry while a
  // dump is enabled. It keeps the dump controls in the always-on power domain, and a hardware reset
  // clears their EN fields, so that no more information is captured until software enables the
  // dump again. This partition stores the dumps.

  // ALERT_REGWEN, ALERT_INFO_CTRL, CPU_REGWEN and CPU_INFO_CTRL are external (hwext). The secondary
  // partition keeps them, and this partition reads them. It forwards a write of 0 to a lock, which
  // clears it (rw0c), decodes the writes to an EN field into a set and a clear, and forwards the
  // writes to an INDEX field. The register file blocks the writes to a control while its lock is
  // clear.

  // ALERT_REGWEN and ALERT_INFO_CTRL.
  assign hw2reg.alert_regwen.d          = intraip_s2p_i.alert_regwen_q;
  assign intraip_p2s_o.alert_regwen_clr = reg2hw.alert_regwen.qe & ~reg2hw.alert_regwen.q;

  assign hw2reg.alert_info_ctrl.en.d    = intraip_s2p_i.alert_info_en_q;
  assign hw2reg.alert_info_ctrl.index.d = intraip_s2p_i.alert_info_idx_q;
  assign intraip_p2s_o.alert_info_en_set =
      reg2hw.alert_info_ctrl.en.qe & reg2hw.alert_info_ctrl.en.q;
  assign intraip_p2s_o.alert_info_en_clr =
      reg2hw.alert_info_ctrl.en.qe & ~reg2hw.alert_info_ctrl.en.q;
  assign intraip_p2s_o.alert_info_idx_we = reg2hw.alert_info_ctrl.index.qe;
  assign intraip_p2s_o.alert_info_idx_wd = reg2hw.alert_info_ctrl.index.q;

  // CPU_REGWEN and CPU_INFO_CTRL.
  assign hw2reg.cpu_regwen.d          = intraip_s2p_i.cpu_regwen_q;
  assign intraip_p2s_o.cpu_regwen_clr = reg2hw.cpu_regwen.qe & ~reg2hw.cpu_regwen.q;

  assign hw2reg.cpu_info_ctrl.en.d    = intraip_s2p_i.cpu_info_en_q;
  assign hw2reg.cpu_info_ctrl.index.d = intraip_s2p_i.cpu_info_idx_q;
  assign intraip_p2s_o.cpu_info_en_set =
      reg2hw.cpu_info_ctrl.en.qe & reg2hw.cpu_info_ctrl.en.q;
  assign intraip_p2s_o.cpu_info_en_clr =
      reg2hw.cpu_info_ctrl.en.qe & ~reg2hw.cpu_info_ctrl.en.q;
  assign intraip_p2s_o.cpu_info_idx_we = reg2hw.cpu_info_ctrl.index.qe;
  assign intraip_p2s_o.cpu_info_idx_wd = reg2hw.cpu_info_ctrl.index.q;

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(alert_handler_pkg::alert_crashdump_t))
  ) u_alert_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(alert_dump_i),
    .dump_capture_i(intraip_s2p_i.alert_dump_capture),
    .slot_sel_i(intraip_s2p_i.alert_info_idx_q),
    .slots_cnt_o(hw2reg.alert_info_attr.d),
    .slot_o(hw2reg.alert_info.d)
  );

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(rv_core_ibex_pkg::cpu_crash_dump_t))
  ) u_cpu_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(cpu_dump_i),
    .dump_capture_i(intraip_s2p_i.cpu_dump_capture),
    .slot_sel_i(intraip_s2p_i.cpu_info_idx_q),
    .slots_cnt_o(hw2reg.cpu_info_attr.d),
    .slot_o(hw2reg.cpu_info.d)
  );


  ////////////////////////////////////////////////////
  // Routing. This partition outputs all the reset asserted indications.
  ////////////////////////////////////////////////////
  assign rst_en_o.por_aon[DomainMainSel] = intraip_s2p_i.rst_en_por_aon_main;
  assign rst_en_o.por_aon[DomainAonSel] = intraip_s2p_i.rst_en_por_aon_aon;
  assign rst_en_o.por_io[DomainAonSel] = intraip_s2p_i.rst_en_por_io_aon;
  assign rst_en_o.lc_aon[DomainAonSel] = intraip_s2p_i.rst_en_lc_aon_aon;
  assign rst_en_o.lc_io[DomainAonSel] = intraip_s2p_i.rst_en_lc_io_aon;
  assign rst_en_o.lc_io_shadowed[DomainAonSel] = intraip_s2p_i.rst_en_lc_io_shadowed_aon;

  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  `ASSERT_INIT(ParameterMatch_A, NumHwResets == pwrmgr_pkg::HwResetWidth)


  // output known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A,    tl_o.d_valid  )
  `ASSERT_KNOWN(TlAReadyKnownO_A,    tl_o.a_ready  )
  `ASSERT_KNOWN(AlertsKnownO_A,      alert_tx_o    )
  `ASSERT_KNOWN(ResetsKnownO_A,      resets_o      )
  `ASSERT_KNOWN(RstEnKnownO_A,       rst_en_o      )

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule // rstmgr_part_primary
