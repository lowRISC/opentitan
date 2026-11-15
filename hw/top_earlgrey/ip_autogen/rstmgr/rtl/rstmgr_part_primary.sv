// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primary partition of the split reset manager.
//
// The primary partition hosts:
//  - the register file and the alerts (ERR_CODE and RESET_INFO are external: the secondary
//    partition keeps their state),
//  - the crash dump capture (ALERT_INFO and CPU_INFO),
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
  input clk_io_div4_i,
  input clk_main_i,
  input clk_io_i,
  input clk_usb_i,
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

  // software initiated reset request
  output mubi4_t sw_rst_req_o,

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

  // The leaf resets that this partition generates but does not output. They only cross to the
  // secondary partition.

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
    .clk_por_i  (clk_por),
    .rst_por_ni (rst_por_n),
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
  logic [21:0] cnsty_chk_errs;
  logic [21:0] fsm_errs;

  // consistency sparse fsm errors

  // ERR_CODE is external, so the register file keeps no state for it. The errors of this partition
  // go to the secondary partition, which keeps the record of all of them in the always-on power
  // domain. ERR_CODE and the alerts read that record.
  assign intraip_p2s_o.reg_intg_err  = reg_intg_err;
  // The clocks that the secondary partition uses, which enter this partition only.
  assign intraip_p2s_o.clk     = clk_i;
  assign intraip_p2s_o.clk_por = clk_por_i;
  assign intraip_p2s_o.clk_io_div4 = clk_io_div4_i;
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

  // The secondary partition generates the source resets (lc and sys).


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
  // Power Domains: ['Main'], hosted in this partition: ['Main']
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
    .rst_en_o(rst_en_o.por_io),
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
  // Generating resets for por_io_div4
  // Power Domains: ['Aon', 'Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_por_io_div4 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_por_aon_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.por_io_div4[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_por_io_div4_n),
    .err_o(cnsty_chk_errs[2]),
    .fsm_err_o(fsm_errs[2])
  );
  if (SecCheck) begin : gen_dmain_por_io_div4_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainPorIoDiv4FsmCheck_A,
    u_dmain_por_io_div4.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for por_usb
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_por_usb (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_usb_i),
    .parent_rst_ni(rst_por_aon_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.por_usb),
    .leaf_rst_o(resets_o.rst_por_usb_n),
    .err_o(cnsty_chk_errs[3]),
    .fsm_err_o(fsm_errs[3])
  );
  if (SecCheck) begin : gen_dmain_por_usb_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainPorUsbFsmCheck_A,
    u_dmain_por_usb.gen_rst_chk.u_rst_chk.u_state_regs,
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
    .err_o(cnsty_chk_errs[4]),
    .fsm_err_o(fsm_errs[4])
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
    .err_o(cnsty_chk_errs[5]),
    .fsm_err_o(fsm_errs[5])
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
    .err_o(cnsty_chk_errs[6]),
    .fsm_err_o(fsm_errs[6])
  );
  if (SecCheck) begin : gen_dmain_lc_aon_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainLcAonFsmCheck_A,
    u_dmain_lc_aon.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for lc_io
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
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
    .rst_en_o(rst_en_o.lc_io),
    .leaf_rst_o(resets_o.rst_lc_io_n),
    .err_o(cnsty_chk_errs[7]),
    .fsm_err_o(fsm_errs[7])
  );
  if (SecCheck) begin : gen_dmain_lc_io_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainLcIoFsmCheck_A,
    u_dmain_lc_io.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for lc_io_div4
  // Power Domains: ['Main', 'Aon'], hosted in this partition: ['Main']
  // Shadowed: True
  rstmgr_leaf_rst #(
    .SecCheck(0),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_io_div4 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_io_div4[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_lc_io_div4_n),
    .err_o(cnsty_chk_errs[8]),
    .fsm_err_o(fsm_errs[8])
  );
  rstmgr_leaf_rst #(
    .SecCheck(0),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_io_div4_shadowed (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_io_div4_shadowed[DomainMainSel]),
    .leaf_rst_o(resets_o.rst_lc_io_div4_shadowed_n),
    .err_o(cnsty_chk_errs[9]),
    .fsm_err_o(fsm_errs[9])
  );
  // Generating resets for lc_usb
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_dmain_lc_usb (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_usb_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.lc_usb),
    .leaf_rst_o(resets_o.rst_lc_usb_n),
    .err_o(cnsty_chk_errs[10]),
    .fsm_err_o(fsm_errs[10])
  );
  if (SecCheck) begin : gen_dmain_lc_usb_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainLcUsbFsmCheck_A,
    u_dmain_lc_usb.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
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
    .err_o(cnsty_chk_errs[11]),
    .fsm_err_o(fsm_errs[11])
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
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[SPI_DEVICE].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.spi_device),
    .leaf_rst_o(resets_o.rst_spi_device_n),
    .err_o(cnsty_chk_errs[12]),
    .fsm_err_o(fsm_errs[12])
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
    .err_o(cnsty_chk_errs[13]),
    .fsm_err_o(fsm_errs[13])
  );
  if (SecCheck) begin : gen_dmain_spi_host0_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainSpiHost0FsmCheck_A,
    u_dmain_spi_host0.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for spi_host1
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_spi_host1 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[SPI_HOST1].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.spi_host1),
    .leaf_rst_o(resets_o.rst_spi_host1_n),
    .err_o(cnsty_chk_errs[14]),
    .fsm_err_o(fsm_errs[14])
  );
  if (SecCheck) begin : gen_dmain_spi_host1_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainSpiHost1FsmCheck_A,
    u_dmain_spi_host1.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for usb
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_usb (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_usb_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[USB].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.usb),
    .leaf_rst_o(resets_o.rst_usb_n),
    .err_o(cnsty_chk_errs[15]),
    .fsm_err_o(fsm_errs[15])
  );
  if (SecCheck) begin : gen_dmain_usb_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainUsbFsmCheck_A,
    u_dmain_usb.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for usb_aon
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_usb_aon (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_aon_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[USB_AON].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.usb_aon),
    .leaf_rst_o(resets_o.rst_usb_aon_n),
    .err_o(cnsty_chk_errs[16]),
    .fsm_err_o(fsm_errs[16])
  );
  if (SecCheck) begin : gen_dmain_usb_aon_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainUsbAonFsmCheck_A,
    u_dmain_usb_aon.gen_rst_chk.u_rst_chk.u_state_regs,
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
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[I2C0].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.i2c0),
    .leaf_rst_o(resets_o.rst_i2c0_n),
    .err_o(cnsty_chk_errs[17]),
    .fsm_err_o(fsm_errs[17])
  );
  if (SecCheck) begin : gen_dmain_i2c0_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainI2c0FsmCheck_A,
    u_dmain_i2c0.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for i2c1
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_i2c1 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[I2C1].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.i2c1),
    .leaf_rst_o(resets_o.rst_i2c1_n),
    .err_o(cnsty_chk_errs[18]),
    .fsm_err_o(fsm_errs[18])
  );
  if (SecCheck) begin : gen_dmain_i2c1_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainI2c1FsmCheck_A,
    u_dmain_i2c1.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for i2c2
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_i2c2 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_div4_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[I2C2].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.i2c2),
    .leaf_rst_o(resets_o.rst_i2c2_n),
    .err_o(cnsty_chk_errs[19]),
    .fsm_err_o(fsm_errs[19])
  );
  if (SecCheck) begin : gen_dmain_i2c2_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainI2c2FsmCheck_A,
    u_dmain_i2c2.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for i3c0
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_i3c0 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[I3C0].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.i3c0),
    .leaf_rst_o(resets_o.rst_i3c0_n),
    .err_o(cnsty_chk_errs[20]),
    .fsm_err_o(fsm_errs[20])
  );
  if (SecCheck) begin : gen_dmain_i3c0_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainI3c0FsmCheck_A,
    u_dmain_i3c0.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end
  // Generating resets for i3c1
  // Power Domains: ['Main'], hosted in this partition: ['Main']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b1)
  ) u_dmain_i3c1 (
    .clk_i,
    .rst_ni,
    .leaf_clk_i(clk_io_i),
    .parent_rst_ni(rst_lc_src_n_main),
    .sw_rst_req_ni(reg2hw.sw_rst_ctrl_n[I3C1].q),
    .scan_rst_ni(scan_rst_n),
    // SEC_CM: SCAN.INTERSIG.MUBI
    .scanmode_i(intraip_s2p_i.scanmode),
    .rst_en_o(rst_en_o.i3c1),
    .leaf_rst_o(resets_o.rst_i3c1_n),
    .err_o(cnsty_chk_errs[21]),
    .fsm_err_o(fsm_errs[21])
  );
  if (SecCheck) begin : gen_dmain_i3c1_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(
    DMainI3c1FsmCheck_A,
    u_dmain_i3c1.gen_rst_chk.u_rst_chk.u_state_regs,
    alert_tx_o[0])
  end

  ////////////////////////////////////////////////////
  // Reset info construction                        //
  ////////////////////////////////////////////////////

  logic rst_hw_req;
  logic rst_low_power;
  logic pwrmgr_rst_req;

  // there is a valid reset request from pwrmgr
  assign pwrmgr_rst_req = |intraip_s2p_i.pwr_rst_lc_req || |intraip_s2p_i.pwr_rst_sys_req;

  // a reset reason is only valid if the related processing element is also reset.
  // In the future, if ever there are multiple processing elements, this code here
  // must be updated to account for each individual core.
  assign rst_hw_req    = pwrmgr_rst_req &
                         (intraip_s2p_i.pwr_reset_cause == pwrmgr_pkg::HwReq);
  assign rst_low_power = pwrmgr_rst_req &
                         (intraip_s2p_i.pwr_reset_cause == pwrmgr_pkg::LowPwrEntry);

  // software initiated reset request
  assign sw_rst_req_o = prim_mubi_pkg::mubi4_t'(reg2hw.reset_req.q);

  // when pwrmgr reset request is received (reset is imminent), clear software
  // request so we are not in an infinite reset loop.
  assign hw2reg.reset_req.de = pwrmgr_rst_req;
  assign hw2reg.reset_req.d  = prim_mubi_pkg::MuBi4False;

  // RESET_INFO is external (hwext). The secondary partition keeps the reset reasons in the
  // always-on power domain, so that they survive a deep sleep. This partition reads them, and
  // forwards the software writes and the software reset request that SW_RESET records.
  assign hw2reg.reset_info        = intraip_s2p_i.reset_info;
  assign intraip_p2s_o.reset_info = reg2hw.reset_info;
  assign intraip_p2s_o.sw_rst_req = sw_rst_req_o;

  ////////////////////////////////////////////////////
  // Crash info capture                             //
  ////////////////////////////////////////////////////

  logic dump_capture;
  assign dump_capture =  rst_hw_req | rst_low_power;

  // halt dump capture once we hit particular conditions
  logic dump_capture_halt;
  assign dump_capture_halt = rst_hw_req;

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(alert_handler_pkg::alert_crashdump_t))
  ) u_alert_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(alert_dump_i),
    .dump_capture_i(dump_capture & reg2hw.alert_info_ctrl.en.q),
    .slot_sel_i(reg2hw.alert_info_ctrl.index.q),
    .slots_cnt_o(hw2reg.alert_info_attr.d),
    .slot_o(hw2reg.alert_info.d)
  );

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(rv_core_ibex_pkg::cpu_crash_dump_t))
  ) u_cpu_info (
    .clk_i(clk_por),
    .rst_ni(rst_por_n),
    .dump_i(cpu_dump_i),
    .dump_capture_i(dump_capture & reg2hw.cpu_info_ctrl.en.q),
    .slot_sel_i(reg2hw.cpu_info_ctrl.index.q),
    .slots_cnt_o(hw2reg.cpu_info_attr.d),
    .slot_o(hw2reg.cpu_info.d)
  );

  // once dump is captured, no more information is captured until
  // re-enabled by software.
  assign hw2reg.alert_info_ctrl.en.d  = 1'b0;
  assign hw2reg.alert_info_ctrl.en.de = dump_capture_halt;
  assign hw2reg.cpu_info_ctrl.en.d  = 1'b0;
  assign hw2reg.cpu_info_ctrl.en.de = dump_capture_halt;

  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  `ASSERT_INIT(ParameterMatch_A, NumHwResets == pwrmgr_pkg::HwResetWidth)


  // output known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A,    tl_o.d_valid  )
  `ASSERT_KNOWN(TlAReadyKnownO_A,    tl_o.a_ready  )
  `ASSERT_KNOWN(AlertsKnownO_A,      alert_tx_o    )
  ////////////////////////////////////////////////////
  // Routing. This partition outputs the resets of the power domain that powers down.
  ////////////////////////////////////////////////////
  assign intraip_p2s_o.rst_lc_io_div4_n_main = resets_o.rst_lc_io_div4_n;

  ////////////////////////////////////////////////////
  // Routing. This partition outputs all the reset asserted indications.
  ////////////////////////////////////////////////////
  assign rst_en_o.por_aon[DomainMainSel] = intraip_s2p_i.rst_en_por_aon_main;
  assign rst_en_o.por_aon[DomainAonSel] = intraip_s2p_i.rst_en_por_aon_aon;
  assign rst_en_o.por_io_div4[DomainAonSel] = intraip_s2p_i.rst_en_por_io_div4_aon;
  assign rst_en_o.lc_aon[DomainAonSel] = intraip_s2p_i.rst_en_lc_aon_aon;
  assign rst_en_o.lc_io_div4[DomainAonSel] = intraip_s2p_i.rst_en_lc_io_div4_aon;
  assign rst_en_o.lc_io_div4_shadowed[DomainAonSel] = intraip_s2p_i.rst_en_lc_io_div4_shadowed_aon;
  assign rst_en_o.sys_io_div4 = intraip_s2p_i.rst_en_sys_io_div4_aon;

  `ASSERT_KNOWN(ResetsKnownO_A,      resets_o      )
  `ASSERT_KNOWN(RstEnKnownO_A,       rst_en_o      )

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule // rstmgr_part_primary
