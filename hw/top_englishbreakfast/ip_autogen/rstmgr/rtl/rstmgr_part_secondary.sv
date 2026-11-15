// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Secondary partition of the split reset manager.
//
// The secondary partition hosts:
//  - the reset roots (por, lc source and sys source),
//  - the POR handling of each power domain,
//  - the leaf resets of the always-on side,
//  - the record of ERR_CODE and the reset reasons of RESET_INFO.
// It receives the always-on clock of its own power domain. Every other clock enters the primary
// partition, which forwards the clocks that this partition uses.
//  - The bus clock, for the consistency checks of its leaf resets and the record of ERR_CODE.
//  - The POR clock, for its reset controllers and RESET_INFO.
//  - The clocks of some of its leaf resets.
// This partition drives the always-on resets directly. Thus they stay out of reset while the power
// domain of the primary partition is off.
`include "prim_assert.sv"

module rstmgr_part_secondary
  import rstmgr_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter bit SecCheck = 1,
  parameter int SecMaxSyncDelay = 2
) (
  // Secondary partition clocks and resets
  input rst_ni,
  input clk_aon_i,
  input rst_por_ni,

  // Scan signals. They come from the DFT source in this partition's power domain, and go on to the
  // primary partition in intraip_s2p_o.
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input scan_rst_ni,

  // POR input
  input [PowerDomains-1:0] por_n_i,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_rst_req_t pwr_i,
  output pwrmgr_pkg::pwr_rst_rsp_t pwr_o,


  // Reset outputs of this partition
  output rstmgr_out_secondary_t resets_secondary_o,

  // inter-partition signalling
  output intraip_s2p_t intraip_s2p_o,
  input intraip_p2s_t intraip_p2s_i
);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  // The clocks that this partition uses and does not receive come from the primary partition.
  //  - intraip_p2s_i.clk: the bus clock, for the consistency checks of the leaf resets and the
  //    record of ERR_CODE.
  //  - intraip_p2s_i.clk_por: the POR clock, for the reset controllers and RESET_INFO.
  //  - The clocks of some leaf resets.

  // The leaf resets that this partition generates but does not output. They only cross to the
  // primary partition.

  // receive POR and stretch
  // The por is at first stretched and synced on clk_aon
  logic [PowerDomains-1:0] rst_por_aon_n;
  // The roots and their reset asserted indications exist for every power domain. The por_aon reset
  // takes the roots and indications of its own power domains, in the shape of the output structs.
  mubi4_t [PowerDomains-1:0] rst_en_por_aon;

  ////////////////////////////////////////////////////
  // Scan mode of the POR roots                     //
  ////////////////////////////////////////////////////

  // The scan mode, with one copy for the root of each power domain. With AsyncOn(0),
  // prim_mubi4_sync only buffers it. Its clock and reset serve only its assertion.
  prim_mubi_pkg::mubi4_t [PowerDomains-1:0] por_scanmode;
  prim_mubi4_sync #(
    .NumCopies(PowerDomains),
    .AsyncOn(0)
  ) u_por_scanmode_sync (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(por_scanmode)
  );

  ////////////////////////////////////////////////////
  // POR root of the Aon power domain               //
  ////////////////////////////////////////////////////

  // The root of the Aon power domain is the stretched POR.
  rstmgr_por u_rst_por_aon (
    .clk_i(clk_aon_i),
    .rst_ni(por_n_i[DomainAonSel]),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(por_scanmode[DomainAonSel])),
    .rst_no(rst_por_aon_n[DomainAonSel])
  );

  // The reset asserted indication of the Aon root, for the alert handler.
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_rst_por_aon_en_sender (
    .clk_i(clk_aon_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .mubi_i(MuBi4False),
    .mubi_o(rst_en_por_aon[DomainAonSel])
  );

  ////////////////////////////////////////////////////
  // POR root of the Main power domain              //
  ////////////////////////////////////////////////////

  // The root of the Main power domain combines the always-on root and the POR (power good) of
  // the Main power domain. It does not release before the always-on root.
  logic rst_por_main_premux;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_por_main_sync (
    .clk_i(clk_aon_i),
    .rst_ni(rst_por_aon_n[DomainAonSel] & por_n_i[DomainMainSel]),
    .d_i(1'b1),
    .q_o(rst_por_main_premux)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_por_main_mux (
    .clk0_i(rst_por_main_premux),
    .clk1_i(scan_rst_ni),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(por_scanmode[DomainMainSel])),
    .clk_o(rst_por_aon_n[DomainMainSel])
  );

  // The reset asserted indication of the Main root, for the alert handler.
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_rst_por_main_en_sender (
    .clk_i(clk_aon_i),
    .rst_ni(rst_por_aon_n[DomainMainSel]),
    .mubi_i(MuBi4False),
    .mubi_o(rst_en_por_aon[DomainMainSel])
  );

  assign resets_secondary_o.rst_por_aon_n[DomainAonSel] = rst_por_aon_n[DomainAonSel];
  assign intraip_s2p_o.rst_en_por_aon_aon = rst_en_por_aon[DomainAonSel];
  assign resets_secondary_o.rst_por_aon_n[DomainMainSel] = rst_por_aon_n[DomainMainSel];
  assign intraip_s2p_o.rst_en_por_aon_main = rst_en_por_aon[DomainMainSel];

  logic clk_por;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_clk_buf (
    .clk_i(intraip_p2s_i.clk_por),
    .clk_o(clk_por)
  );

  logic rst_por_n;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_por_rst_buf (
    .clk_i(rst_por_ni),
    .clk_o(rst_por_n)
  );

  ////////////////////////////////////////////////////
  // Source resets in the system                    //
  // These are hardcoded and not directly used.     //
  // Instead they act as async reset roots.         //
  ////////////////////////////////////////////////////

  // The lc and sys source controllers share the POR roots as their parents. An lc reset does not
  // imply a sys reset structurally. The power manager requests both together, except for a
  // non-debug-module reset with debug enabled, which resets the lc domain alone.

  logic [PowerDomains-1:0] rst_lc_src_n;
  logic [PowerDomains-1:0] rst_sys_src_n;

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] rst_ctrl_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_ctrl_scanmode_sync (
    .clk_i (clk_por),
    .rst_ni (rst_por_n),
    .mubi_i(scanmode_i),
    .mubi_o(rst_ctrl_scanmode)
  );

  // lc reset sources
  rstmgr_ctrl u_lc_src (
    .clk_i (clk_por),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(rst_ctrl_scanmode[0])),
    .scan_rst_ni(scan_rst_ni),
    .rst_req_i(pwr_i.rst_lc_req),
    .rst_parent_ni(rst_por_aon_n),
    .rst_no(rst_lc_src_n)
  );

  // sys reset sources
  rstmgr_ctrl u_sys_src (
    .clk_i (clk_por),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(rst_ctrl_scanmode[0])),
    .scan_rst_ni(scan_rst_ni),
    .rst_req_i(pwr_i.rst_sys_req),
    .rst_parent_ni(rst_por_aon_n),
    .rst_no(rst_sys_src_n)
  );

  assign pwr_o.rst_lc_src_n = rst_lc_src_n;
  assign pwr_o.rst_sys_src_n = rst_sys_src_n;

  ////////////////////////////////////////////////////
  // Errors of this partition's leaf resets         //
  ////////////////////////////////////////////////////
  logic [4:0] cnsty_chk_errs;
  logic [4:0] fsm_errs;

  ////////////////////////////////////////////////////
  // Leaf resets of the secondary partition         //
  // The primary partition generates every other    //
  // leaf reset.                                    //
  ////////////////////////////////////////////////////
  // Generating resets for por_io_div4
  // Power Domains: ['Aon', 'Main'], hosted in this partition: ['Aon']
  // Shadowed: True
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_daon_por_io_div4 (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .leaf_clk_i(intraip_p2s_i.clk_io_div4),
    .parent_rst_ni(rst_por_aon_n[DomainAonSel]),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(scanmode_i),
    .rst_en_o(intraip_s2p_o.rst_en_por_io_div4_aon),
    .leaf_rst_o(resets_secondary_o.rst_por_io_div4_n),
    .err_o(cnsty_chk_errs[0]),
    .fsm_err_o(fsm_errs[0])
  );
  // The assertion uses _ERR rather than _ALERT on purpose, as this partition has no alert. The FSM
  // error leaves this partition through intraip_s2p_o.fsm_err_q, and the primary partition turns it
  // into its fatal alert.
  if (SecCheck) begin : gen_daon_por_io_div4_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(
    DAonPorIoDiv4FsmCheck_A,
    u_daon_por_io_div4.gen_rst_chk.u_rst_chk.u_state_regs,
    intraip_s2p_o.fsm_err_q, 0, 2, intraip_p2s_i.clk, !rst_ni)
  end
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_daon_por_io_div4_shadowed (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .leaf_clk_i(intraip_p2s_i.clk_io_div4),
    .parent_rst_ni(rst_por_aon_n[DomainAonSel]),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(scanmode_i),
    .rst_en_o(intraip_s2p_o.rst_en_por_io_div4_shadowed_aon),
    .leaf_rst_o(resets_secondary_o.rst_por_io_div4_shadowed_n),
    .err_o(cnsty_chk_errs[1]),
    .fsm_err_o(fsm_errs[1])
  );
  // The assertion uses _ERR rather than _ALERT on purpose, as this partition has no alert. The FSM
  // error leaves this partition through intraip_s2p_o.fsm_err_q, and the primary partition turns it
  // into its fatal alert.
  if (SecCheck) begin : gen_daon_por_io_div4_shadowed_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(
    DAonPorIoDiv4ShadowedFsmCheck_A,
    u_daon_por_io_div4_shadowed.gen_rst_chk.u_rst_chk.u_state_regs,
    intraip_s2p_o.fsm_err_q, 0, 2, intraip_p2s_i.clk, !rst_ni)
  end
  // Generating resets for lc_io_div4
  // Power Domains: ['Main', 'Aon'], hosted in this partition: ['Aon']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(0),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_daon_lc_io_div4 (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .leaf_clk_i(intraip_p2s_i.clk_io_div4),
    .parent_rst_ni(rst_lc_src_n[DomainAonSel]),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(scanmode_i),
    .rst_en_o(intraip_s2p_o.rst_en_lc_io_div4_aon),
    .leaf_rst_o(resets_secondary_o.rst_lc_io_div4_n),
    .err_o(cnsty_chk_errs[2]),
    .fsm_err_o(fsm_errs[2])
  );
  // Generating resets for sys_io_div4
  // Power Domains: ['Main', 'Aon'], hosted in this partition: ['Aon']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_daon_sys_io_div4 (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .leaf_clk_i(intraip_p2s_i.clk_io_div4),
    .parent_rst_ni(rst_sys_src_n[DomainAonSel]),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(scanmode_i),
    .rst_en_o(intraip_s2p_o.rst_en_sys_io_div4_aon),
    .leaf_rst_o(resets_secondary_o.rst_sys_io_div4_n),
    .err_o(cnsty_chk_errs[3]),
    .fsm_err_o(fsm_errs[3])
  );
  // The assertion uses _ERR rather than _ALERT on purpose, as this partition has no alert. The FSM
  // error leaves this partition through intraip_s2p_o.fsm_err_q, and the primary partition turns it
  // into its fatal alert.
  if (SecCheck) begin : gen_daon_sys_io_div4_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(
    DAonSysIoDiv4FsmCheck_A,
    u_daon_sys_io_div4.gen_rst_chk.u_rst_chk.u_state_regs,
    intraip_s2p_o.fsm_err_q, 0, 2, intraip_p2s_i.clk, !rst_ni)
  end
  // Generating resets for sys_aon
  // Power Domains: ['Main', 'Aon'], hosted in this partition: ['Aon']
  // Shadowed: False
  rstmgr_leaf_rst #(
    .SecCheck(SecCheck),
    .SecMaxSyncDelay(SecMaxSyncDelay),
    .SwRstReq(1'b0)
  ) u_daon_sys_aon (
    .clk_i(intraip_p2s_i.clk),
    .rst_ni,
    .leaf_clk_i(clk_aon_i),
    .parent_rst_ni(rst_sys_src_n[DomainAonSel]),
    .sw_rst_req_ni(1'b1),
    .scan_rst_ni(scan_rst_ni),
    .scanmode_i(scanmode_i),
    .rst_en_o(intraip_s2p_o.rst_en_sys_aon_aon),
    .leaf_rst_o(resets_secondary_o.rst_sys_aon_n),
    .err_o(cnsty_chk_errs[4]),
    .fsm_err_o(fsm_errs[4])
  );
  // The assertion uses _ERR rather than _ALERT on purpose, as this partition has no alert. The FSM
  // error leaves this partition through intraip_s2p_o.fsm_err_q, and the primary partition turns it
  // into its fatal alert.
  if (SecCheck) begin : gen_daon_sys_aon_assert
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(
    DAonSysAonFsmCheck_A,
    u_daon_sys_aon.gen_rst_chk.u_rst_chk.u_state_regs,
    intraip_s2p_o.fsm_err_q, 0, 2, intraip_p2s_i.clk, !rst_ni)
  end

  ////////////////////////////////////////////////////
  // Signalling to the primary partition            //
  ////////////////////////////////////////////////////
  assign intraip_s2p_o.rst_por_aon_n_main = rst_por_aon_n[DomainMainSel];
  assign intraip_s2p_o.rst_lc_src_n_main = rst_lc_src_n[DomainMainSel];
  assign intraip_s2p_o.rst_sys_src_n_main = rst_sys_src_n[DomainMainSel];
  assign intraip_s2p_o.pwr_rst_lc_req       = pwr_i.rst_lc_req;
  assign intraip_s2p_o.pwr_rst_sys_req      = pwr_i.rst_sys_req;
  assign intraip_s2p_o.pwr_reset_cause      = pwr_i.reset_cause;

  // The scan signals enter this partition only. The primary partition gets them from here.
  assign intraip_s2p_o.scanmode             = scanmode_i;
  assign intraip_s2p_o.scan_rst_n           = scan_rst_ni;

  ////////////////////////////////////////////////////
  // Reset info (RESET_INFO)                        //
  ////////////////////////////////////////////////////

  // RESET_INFO is external (hwext). This partition keeps the reset reasons in the always-on power
  // domain, on the POR clock and the POR reset. Thus the reasons operate the same as register
  // fields. The POR sets the POR bit, and only the POR resets the reasons. The primary partition
  // reads the reasons and forwards the software writes. Software clears a reason when it writes 1
  // to it (rw1c). The hardware sets a reason. If the hardware sets a reason and software clears it
  // in the same cycle, the set wins.
  logic pwrmgr_rst_req, rst_hw_req, rst_low_power;
  assign pwrmgr_rst_req = |pwr_i.rst_lc_req || |pwr_i.rst_sys_req;
  // A reset reason is only valid if the related processing element is also reset.
  assign rst_hw_req    = pwrmgr_rst_req && (pwr_i.reset_cause == pwrmgr_pkg::HwReq);
  assign rst_low_power = pwrmgr_rst_req && (pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry);

  rstmgr_reg_pkg::rstmgr_hw2reg_reset_info_reg_t reset_info_q;
  rstmgr_reg_pkg::rstmgr_reg2hw_reset_info_reg_t reset_info_wr;
  assign reset_info_wr = intraip_p2s_i.reset_info;

  // RESET_INFO's storage runs on the POR clock, and is reset by the POR of this power domain on
  // that clock (resets_secondary_o.rst_por_io_div4_n).
  always_ff @(posedge clk_por or negedge resets_secondary_o.rst_por_io_div4_n) begin
    if (!resets_secondary_o.rst_por_io_div4_n) begin
      reset_info_q.por.d            <= 1'b1;
      reset_info_q.low_power_exit.d <= 1'b0;
      reset_info_q.sw_reset.d       <= 1'b0;
      reset_info_q.hw_req.d         <= '0;
    end else begin
      if (reset_info_wr.por.qe && reset_info_wr.por.q) begin
        reset_info_q.por.d <= 1'b0;
      end
      if (reset_info_wr.low_power_exit.qe && reset_info_wr.low_power_exit.q) begin
        reset_info_q.low_power_exit.d <= 1'b0;
      end
      if (reset_info_wr.sw_reset.qe && reset_info_wr.sw_reset.q) begin
        reset_info_q.sw_reset.d <= 1'b0;
      end
      if (reset_info_wr.hw_req.qe) begin
        reset_info_q.hw_req.d <= reset_info_q.hw_req.d & ~reset_info_wr.hw_req.q;
      end
      if (rst_low_power) begin
        reset_info_q.low_power_exit.d <= 1'b1;
      end
      // A software reset request triggers the same response as a hardware one, but is recorded
      // apart from it.
      if (rst_hw_req) begin
        reset_info_q.sw_reset.d <=
            prim_mubi_pkg::mubi4_test_true_strict(intraip_p2s_i.sw_rst_req) ||
            reset_info_q.sw_reset.d;
        reset_info_q.hw_req.d   <= pwr_i.rstreqs | reset_info_q.hw_req.d;
      end
    end
  end

  assign intraip_s2p_o.reset_info = reset_info_q;
  // The store of the ERR_CODE CSR, whose register type is hwext. One bit per field:
  //  - REG_INTG_ERR: the integrity error of the register file.
  //  - RESET_CONSISTENCY_ERR: the consistency errors of the leaves of both partitions.
  //  - FSM_ERR: the FSM errors of the leaves of both partitions.
  // They are kept here, in the secondary partition, as it is always in the Aon power domain. This
  // keeps them through a deep sleep cycle, and captures tampering with the Aon resets, under these
  // requirements:
  //  - The checkers' clock must run until their resets assert. A detection made while it is off,
  //    on entering deep sleep or later, is lost.
  //  - While the primary partition's power domain is off, its isolation must clamp the error bits
  //    of intraip_p2s_i to 0. Otherwise these bits would latch a false error.
  //  - The record runs on the bus clock that the primary partition forwards, the clock on which
  //    that partition detects its errors, so these bits need no synchronizer.
  // Note: the reset that an escalation triggers must clear these bits, or the alert would fire
  // again after the escalation.
  logic cnsty_chk_err, fsm_err;
  logic reg_intg_err_q, cnsty_chk_err_q, fsm_err_q;
  assign cnsty_chk_err = |cnsty_chk_errs || intraip_p2s_i.cnsty_chk_err;
  assign fsm_err       = |fsm_errs || intraip_p2s_i.fsm_err;

  // The record uses the bus clock, because the primary partition detects these errors on the bus
  // clock. Thus the record needs no synchronizer. The lc reset of this power domain on that clock
  // resets the record. Thus an escalation's reset clears the record, but a deep sleep does not.
  // That reset is resets_secondary_o.rst_lc_io_div4_n.
  logic err_code_rst_n;
  assign err_code_rst_n = resets_secondary_o.rst_lc_io_div4_n;
  always_ff @(posedge intraip_p2s_i.clk or negedge err_code_rst_n) begin
    if (!err_code_rst_n) begin
      reg_intg_err_q  <= 1'b0;
      cnsty_chk_err_q <= 1'b0;
      fsm_err_q       <= 1'b0;
    end else begin
      reg_intg_err_q  <= reg_intg_err_q || intraip_p2s_i.reg_intg_err;
      cnsty_chk_err_q <= cnsty_chk_err_q || cnsty_chk_err;
      fsm_err_q       <= fsm_err_q || fsm_err;
    end
  end

  assign intraip_s2p_o.reg_intg_err_q         = reg_intg_err_q;
  assign intraip_s2p_o.cnsty_chk_err_q        = cnsty_chk_err_q;
  assign intraip_s2p_o.fsm_err_q              = fsm_err_q;

  `ASSERT(RegIntgErrRecordSticky_A, reg_intg_err_q |=> reg_intg_err_q, intraip_p2s_i.clk,
          !err_code_rst_n)
  `ASSERT(CnstyChkErrRecordSticky_A, cnsty_chk_err_q |=> cnsty_chk_err_q, intraip_p2s_i.clk,
          !err_code_rst_n)
  `ASSERT(FsmErrRecordSticky_A, fsm_err_q |=> fsm_err_q, intraip_p2s_i.clk,
          !err_code_rst_n)

  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////
  `ASSERT_KNOWN(PwrKnownO_A,         pwr_o, intraip_p2s_i.clk, !rst_ni)
  ////////////////////////////////////////////////////
  // Routing. This partition outputs the resets of the modules of the always-on power domain.
  ////////////////////////////////////////////////////

  // The reset asserted indications that this partition generates go to the primary partition, which
  // outputs them. Each leaf drives its field of intraip_s2p_o directly.

  `ASSERT_KNOWN(ResetsKnownO_A,      resets_secondary_o, intraip_p2s_i.clk, !rst_ni)
  `ASSERT_KNOWN(IntraipKnownO_A,   intraip_s2p_o, intraip_p2s_i.clk, !rst_ni)
endmodule // rstmgr_part_secondary
