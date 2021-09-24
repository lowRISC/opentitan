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
// This module is the overall reset manager wrapper

`include "prim_assert.sv"

// This top level controller is fairly hardcoded right now, but will be switched to a template
module rstmgr
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Primary module clocks
  input clk_i,
  input rst_ni,
  input clk_aon_i,
  input clk_io_div4_i,
  input clk_main_i,
  input clk_io_i,
  input clk_io_div2_i,
  input clk_usb_i,

  // POR input
  input [PowerDomains-1:0] por_n_i,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_rst_req_t pwr_i,
  output pwrmgr_pkg::pwr_rst_rsp_t pwr_o,

  // cpu related inputs
  input logic rst_cpu_n_i,
  input logic ndmreset_req_i,

  // Interface to alert handler
  input alert_pkg::alert_crashdump_t alert_dump_i,

  // Interface to cpu crash dump
  input ibex_pkg::crash_dump_t cpu_dump_i,

  // dft bypass
  input scan_rst_ni,
  input lc_ctrl_pkg::lc_tx_t scanmode_i,

  // Reset asserted indications going to alert handler
  output rstmgr_rst_en_t rst_en_o,

  // reset outputs
  output rstmgr_out_t resets_o

);

  import rstmgr_reg_pkg::*;

  // receive POR and stretch
  // The por is at first stretched and synced on clk_aon
  // The rst_ni and pok_i input will be changed once AST is integrated
  logic [PowerDomains-1:0] rst_por_aon_n;

  for (genvar i = 0; i < PowerDomains; i++) begin : gen_rst_por_aon

      lc_ctrl_pkg::lc_tx_t por_scanmode;
      prim_lc_sync #(
        .NumCopies(1),
        .AsyncOn(0)
      ) u_por_scanmode_sync (
        .clk_i(1'b0),  // unused clock
        .rst_ni(1'b1), // unused reset
        .lc_en_i(scanmode_i),
        .lc_en_o(por_scanmode)
      );

    if (i == DomainAonSel) begin : gen_rst_por_aon_normal
      rstmgr_por u_rst_por_aon (
        .clk_i(clk_aon_i),
        .rst_ni(por_n_i[i]),
        .scan_rst_ni,
        .scanmode_i(por_scanmode == lc_ctrl_pkg::On),
        .rst_no(rst_por_aon_n[i])
      );

      // reset asserted indication for alert handler
      prim_lc_sender #(
        .ResetValueIsOn(1)
      ) u_prim_lc_sender (
        .clk_i(clk_aon_i),
        .rst_ni(rst_por_aon_n[i]),
        .lc_en_i(lc_ctrl_pkg::Off),
        .lc_en_o(rst_en_o.rst_por_aon[i])
      );
    end else begin : gen_rst_por_domain
      logic rst_por_aon_premux;
      prim_flop_2sync #(
        .Width(1),
        .ResetValue('0)
      ) u_por_domain_sync (
        .clk_i(clk_aon_i),
        // do not release from reset if aon has not
        .rst_ni(rst_por_aon_n[DomainAonSel] & por_n_i[i]),
        .d_i(1'b1),
        .q_o(rst_por_aon_premux)
      );

      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_por_domain_mux (
        .clk0_i(rst_por_aon_premux),
        .clk1_i(scan_rst_ni),
        .sel_i(por_scanmode == lc_ctrl_pkg::On),
        .clk_o(rst_por_aon_n[i])
      );

      // reset asserted indication for alert handler
      prim_lc_sender #(
        .ResetValueIsOn(1)
      ) u_prim_lc_sender (
        .clk_i(clk_aon_i),
        .rst_ni(rst_por_aon_n[i]),
        .lc_en_i(lc_ctrl_pkg::Off),
        .lc_en_o(rst_en_o.rst_por_aon[i])
      );
    end
  end
  assign resets_o.rst_por_aon_n = rst_por_aon_n;

  ////////////////////////////////////////////////////
  // Register Interface                             //
  ////////////////////////////////////////////////////

  logic [NumAlerts-1:0] alert_test, alerts;
  rstmgr_reg_pkg::rstmgr_reg2hw_t reg2hw;
  rstmgr_reg_pkg::rstmgr_hw2reg_t hw2reg;

  rstmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(alerts[0]),
    .devmode_i(1'b1)
  );

  ////////////////////////////////////////////////////
  // Alerts                                         //
  ////////////////////////////////////////////////////

  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////////////////////////////////////////
  // Input handling                                 //
  ////////////////////////////////////////////////////

  logic ndmreset_req_q;
  logic ndm_req_valid;

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_ndm_sync (
    .clk_i,
    .rst_ni,
    .d_i(ndmreset_req_i),
    .q_o(ndmreset_req_q)
  );

  assign ndm_req_valid = ndmreset_req_q & (pwr_i.reset_cause == pwrmgr_pkg::ResetNone);

  ////////////////////////////////////////////////////
  // Source resets in the system                    //
  // These are hardcoded and not directly used.     //
  // Instead they act as async reset roots.         //
  ////////////////////////////////////////////////////

  // The two source reset modules are chained together.  The output of one is fed into the
  // the second.  This ensures that if upstream resets for any reason, the associated downstream
  // reset will also reset.

  logic [PowerDomains-1:0] rst_lc_src_n;
  logic [PowerDomains-1:0] rst_sys_src_n;

  lc_ctrl_pkg::lc_tx_t rst_ctrl_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_ctrl_scanmode_sync (
    .clk_i(1'b0),  // unused clock
    .rst_ni(1'b1), // unused reset
    .lc_en_i(scanmode_i),
    .lc_en_o(rst_ctrl_scanmode)
  );

  // lc reset sources
  rstmgr_ctrl u_lc_src (
    .clk_i,
    .scanmode_i(rst_ctrl_scanmode == lc_ctrl_pkg::On),
    .scan_rst_ni,
    .rst_ni,
    .rst_req_i(pwr_i.rst_lc_req),
    .rst_parent_ni({PowerDomains{1'b1}}),
    .rst_no(rst_lc_src_n)
  );

  // sys reset sources
  rstmgr_ctrl u_sys_src (
    .clk_i,
    .scanmode_i(rst_ctrl_scanmode == lc_ctrl_pkg::On),
    .scan_rst_ni,
    .rst_ni,
    .rst_req_i(pwr_i.rst_sys_req | {PowerDomains{ndm_req_valid}}),
    .rst_parent_ni(rst_lc_src_n),
    .rst_no(rst_sys_src_n)
  );

  assign pwr_o.rst_lc_src_n = rst_lc_src_n;
  assign pwr_o.rst_sys_src_n = rst_sys_src_n;


  ////////////////////////////////////////////////////
  // Software reset controls external reg           //
  ////////////////////////////////////////////////////
  logic [NumSwResets-1:0] sw_rst_ctrl_n;

  for (genvar i=0; i < NumSwResets; i++) begin : gen_sw_rst_ext_regs
    prim_subreg #(
      .DW(1),
      .SwAccess(prim_subreg_pkg::SwAccessRW),
      .RESVAL(1)
    ) u_rst_sw_ctrl_reg (
      .clk_i,
      .rst_ni,
      .we(reg2hw.sw_rst_ctrl_n[i].qe & reg2hw.sw_rst_regwen[i]),
      .wd(reg2hw.sw_rst_ctrl_n[i].q),
      .de('0),
      .d('0),
      .qe(),
      .q(sw_rst_ctrl_n[i]),
      .qs(hw2reg.sw_rst_ctrl_n[i].d)
    );
  end

  ////////////////////////////////////////////////////
  // leaf reset in the system                       //
  // These should all be generated                  //
  ////////////////////////////////////////////////////
  // To simplify generation, each reset generates all associated power domain outputs.
  // If a reset does not support a particular power domain, that reset is always hard-wired to 0.

  lc_ctrl_pkg::lc_tx_t [20:0] leaf_rst_scanmode;
  prim_lc_sync #(
    .NumCopies(21),
    .AsyncOn(0)
    ) u_leaf_rst_scanmode_sync  (
    .clk_i(1'b0),  // unused clock
    .rst_ni(1'b1), // unused reset
    .lc_en_i(scanmode_i),
    .lc_en_o(leaf_rst_scanmode)
 );

  // Generating resets for por
  // Power Domains: ['Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_por_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por (
    .clk_i(clk_main_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_mux (
    .clk0_i(rst_por_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[0] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_por_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_por_domain_aon (
    .clk_i(clk_main_i),
    .rst_ni(rst_por_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_por[DomainAonSel])
  );
  assign rst_por_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_n[Domain0Sel] = rst_por_n[Domain0Sel];
  assign rst_en_o.rst_por[Domain0Sel] = lc_ctrl_pkg::On;
  // Generating resets for por_io
  // Power Domains: ['Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_por_io_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_io (
    .clk_i(clk_io_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_io_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_io_mux (
    .clk0_i(rst_por_io_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[1] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_por_io_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_por_io_domain_aon (
    .clk_i(clk_io_i),
    .rst_ni(rst_por_io_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_por_io[DomainAonSel])
  );
  assign rst_por_io_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_io_n[Domain0Sel] = rst_por_io_n[Domain0Sel];
  assign rst_en_o.rst_por_io[Domain0Sel] = lc_ctrl_pkg::On;
  // Generating resets for por_io_div2
  // Power Domains: ['Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_por_io_div2_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_io_div2 (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_io_div2_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_io_div2_mux (
    .clk0_i(rst_por_io_div2_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[2] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_por_io_div2_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_por_io_div2_domain_aon (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_por_io_div2_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_por_io_div2[DomainAonSel])
  );
  assign rst_por_io_div2_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_io_div2_n[Domain0Sel] = rst_por_io_div2_n[Domain0Sel];
  assign rst_en_o.rst_por_io_div2[Domain0Sel] = lc_ctrl_pkg::On;
  // Generating resets for por_io_div4
  // Power Domains: ['Aon', '0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_por_io_div4_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_io_div4_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_io_div4_mux (
    .clk0_i(rst_por_io_div4_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[3] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_por_io_div4_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_por_io_div4_domain_aon (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_por_io_div4_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_por_io_div4[DomainAonSel])
  );
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_por_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_por_aon_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_por_io_div4_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_por_io_div4_mux (
    .clk0_i(rst_por_io_div4_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[3] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_por_io_div4_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_por_io_div4_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_por_io_div4_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_por_io_div4[Domain0Sel])
  );
  // Generating resets for por_usb
  // Power Domains: ['Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_por_usb_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_por_usb (
    .clk_i(clk_usb_i),
    .rst_ni(rst_por_aon_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_por_usb_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_por_usb_mux (
    .clk0_i(rst_por_usb_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[4] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_por_usb_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_por_usb_domain_aon (
    .clk_i(clk_usb_i),
    .rst_ni(rst_por_usb_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_por_usb[DomainAonSel])
  );
  assign rst_por_usb_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_por_usb_n[Domain0Sel] = rst_por_usb_n[Domain0Sel];
  assign rst_en_o.rst_por_usb[Domain0Sel] = lc_ctrl_pkg::On;
  // Generating resets for lc
  // Power Domains: ['0']
  // Shadowed: True
  logic [PowerDomains-1:0] rst_lc_n;
  assign rst_lc_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_lc_n[DomainAonSel] = rst_lc_n[DomainAonSel];
  assign rst_en_o.rst_lc[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_lc (
    .clk_i(clk_main_i),
    .rst_ni(rst_lc_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_lc_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_lc_mux (
    .clk0_i(rst_lc_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[5] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_domain_0 (
    .clk_i(clk_main_i),
    .rst_ni(rst_lc_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc[Domain0Sel])
  );
  logic [PowerDomains-1:0] rst_lc_shadowed_n;
  assign rst_lc_shadowed_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_lc_shadowed_n[DomainAonSel] = rst_lc_shadowed_n[DomainAonSel];
  assign rst_en_o.rst_lc_shadowed[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_lc_shadowed (
    .clk_i(clk_main_i),
    .rst_ni(rst_lc_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_lc_shadowed_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_lc_shadowed_mux (
    .clk0_i(rst_lc_shadowed_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[5] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_shadowed_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_shadowed_domain_0 (
    .clk_i(clk_main_i),
    .rst_ni(rst_lc_shadowed_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc_shadowed[Domain0Sel])
  );
  // Generating resets for lc_io_div4
  // Power Domains: ['0', 'Aon']
  // Shadowed: True
  logic [PowerDomains-1:0] rst_lc_io_div4_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_lc_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_lc_io_div4_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_lc_io_div4_mux (
    .clk0_i(rst_lc_io_div4_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[6] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_io_div4_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_io_div4_domain_aon (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_io_div4_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc_io_div4[DomainAonSel])
  );
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_lc_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_lc_io_div4_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_lc_io_div4_mux (
    .clk0_i(rst_lc_io_div4_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[6] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_io_div4_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_io_div4_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_io_div4_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc_io_div4[Domain0Sel])
  );
  logic [PowerDomains-1:0] rst_lc_io_div4_shadowed_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_lc_io_div4_shadowed (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_lc_io_div4_shadowed_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_lc_io_div4_shadowed_mux (
    .clk0_i(rst_lc_io_div4_shadowed_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[6] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_io_div4_shadowed_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_io_div4_shadowed_domain_aon (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_io_div4_shadowed_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc_io_div4_shadowed[DomainAonSel])
  );
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_lc_io_div4_shadowed (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_lc_io_div4_shadowed_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_lc_io_div4_shadowed_mux (
    .clk0_i(rst_lc_io_div4_shadowed_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[6] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_io_div4_shadowed_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_io_div4_shadowed_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_lc_io_div4_shadowed_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc_io_div4_shadowed[Domain0Sel])
  );
  // Generating resets for lc_aon
  // Power Domains: ['Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_lc_aon_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_lc_aon (
    .clk_i(clk_aon_i),
    .rst_ni(rst_lc_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_lc_aon_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_lc_aon_mux (
    .clk0_i(rst_lc_aon_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[7] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_lc_aon_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_lc_aon_domain_aon (
    .clk_i(clk_aon_i),
    .rst_ni(rst_lc_aon_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_lc_aon[DomainAonSel])
  );
  assign rst_lc_aon_n[Domain0Sel] = 1'b0;
  assign resets_o.rst_lc_aon_n[Domain0Sel] = rst_lc_aon_n[Domain0Sel];
  assign rst_en_o.rst_lc_aon[Domain0Sel] = lc_ctrl_pkg::On;
  // Generating resets for sys
  // Power Domains: ['0']
  // Shadowed: True
  logic [PowerDomains-1:0] rst_sys_n;
  assign rst_sys_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_sys_n[DomainAonSel] = rst_sys_n[DomainAonSel];
  assign rst_en_o.rst_sys[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys (
    .clk_i(clk_main_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_mux (
    .clk0_i(rst_sys_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[8] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_sys_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_sys_domain_0 (
    .clk_i(clk_main_i),
    .rst_ni(rst_sys_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_sys[Domain0Sel])
  );
  logic [PowerDomains-1:0] rst_sys_shadowed_n;
  assign rst_sys_shadowed_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_sys_shadowed_n[DomainAonSel] = rst_sys_shadowed_n[DomainAonSel];
  assign rst_en_o.rst_sys_shadowed[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys_shadowed (
    .clk_i(clk_main_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_shadowed_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_shadowed_mux (
    .clk0_i(rst_sys_shadowed_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[8] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_sys_shadowed_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_sys_shadowed_domain_0 (
    .clk_i(clk_main_i),
    .rst_ni(rst_sys_shadowed_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_sys_shadowed[Domain0Sel])
  );
  // Generating resets for sys_io_div4
  // Power Domains: ['0', 'Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_sys_io_div4_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_sys_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_sys_io_div4_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_sys_io_div4_mux (
    .clk0_i(rst_sys_io_div4_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[9] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_sys_io_div4_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_sys_io_div4_domain_aon (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_io_div4_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_sys_io_div4[DomainAonSel])
  );
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys_io_div4 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_io_div4_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_io_div4_mux (
    .clk0_i(rst_sys_io_div4_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[9] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_sys_io_div4_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_sys_io_div4_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_io_div4_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_sys_io_div4[Domain0Sel])
  );
  // Generating resets for sys_aon
  // Power Domains: ['0', 'Aon']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_sys_aon_n;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_sys_aon (
    .clk_i(clk_aon_i),
    .rst_ni(rst_sys_src_n[DomainAonSel]),
    .d_i(1'b1),
    .q_o(rst_sys_aon_n[DomainAonSel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_aon_sys_aon_mux (
    .clk0_i(rst_sys_aon_n[DomainAonSel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[10] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_sys_aon_n[DomainAonSel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_sys_aon_domain_aon (
    .clk_i(clk_aon_i),
    .rst_ni(rst_sys_aon_n[DomainAonSel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_sys_aon[DomainAonSel])
  );
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_sys_aon (
    .clk_i(clk_aon_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(1'b1),
    .q_o(rst_sys_aon_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_sys_aon_mux (
    .clk0_i(rst_sys_aon_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[10] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_sys_aon_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_sys_aon_domain_0 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_sys_aon_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_sys_aon[Domain0Sel])
  );
  // Generating resets for spi_device
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_spi_device_n;
  assign rst_spi_device_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_spi_device_n[DomainAonSel] = rst_spi_device_n[DomainAonSel];
  assign rst_en_o.rst_spi_device[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_spi_device (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[SPI_DEVICE]),
    .q_o(rst_spi_device_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_spi_device_mux (
    .clk0_i(rst_spi_device_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[11] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_spi_device_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_spi_device_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_spi_device_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_spi_device[Domain0Sel])
  );
  // Generating resets for spi_host0
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_spi_host0_n;
  assign rst_spi_host0_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_spi_host0_n[DomainAonSel] = rst_spi_host0_n[DomainAonSel];
  assign rst_en_o.rst_spi_host0[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_spi_host0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[SPI_HOST0]),
    .q_o(rst_spi_host0_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_spi_host0_mux (
    .clk0_i(rst_spi_host0_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[12] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_spi_host0_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_spi_host0_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_spi_host0_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_spi_host0[Domain0Sel])
  );
  // Generating resets for spi_host0_core
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_spi_host0_core_n;
  assign rst_spi_host0_core_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_spi_host0_core_n[DomainAonSel] = rst_spi_host0_core_n[DomainAonSel];
  assign rst_en_o.rst_spi_host0_core[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_spi_host0_core (
    .clk_i(clk_io_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[SPI_HOST0_CORE]),
    .q_o(rst_spi_host0_core_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_spi_host0_core_mux (
    .clk0_i(rst_spi_host0_core_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[13] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_spi_host0_core_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_spi_host0_core_domain_0 (
    .clk_i(clk_io_i),
    .rst_ni(rst_spi_host0_core_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_spi_host0_core[Domain0Sel])
  );
  // Generating resets for spi_host1
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_spi_host1_n;
  assign rst_spi_host1_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_spi_host1_n[DomainAonSel] = rst_spi_host1_n[DomainAonSel];
  assign rst_en_o.rst_spi_host1[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_spi_host1 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[SPI_HOST1]),
    .q_o(rst_spi_host1_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_spi_host1_mux (
    .clk0_i(rst_spi_host1_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[14] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_spi_host1_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_spi_host1_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_spi_host1_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_spi_host1[Domain0Sel])
  );
  // Generating resets for spi_host1_core
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_spi_host1_core_n;
  assign rst_spi_host1_core_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_spi_host1_core_n[DomainAonSel] = rst_spi_host1_core_n[DomainAonSel];
  assign rst_en_o.rst_spi_host1_core[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_spi_host1_core (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[SPI_HOST1_CORE]),
    .q_o(rst_spi_host1_core_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_spi_host1_core_mux (
    .clk0_i(rst_spi_host1_core_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[15] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_spi_host1_core_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_spi_host1_core_domain_0 (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_spi_host1_core_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_spi_host1_core[Domain0Sel])
  );
  // Generating resets for usb
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_usb_n;
  assign rst_usb_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_usb_n[DomainAonSel] = rst_usb_n[DomainAonSel];
  assign rst_en_o.rst_usb[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_usb (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[USB]),
    .q_o(rst_usb_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_usb_mux (
    .clk0_i(rst_usb_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[16] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_usb_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_usb_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_usb_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_usb[Domain0Sel])
  );
  // Generating resets for usbif
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_usbif_n;
  assign rst_usbif_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_usbif_n[DomainAonSel] = rst_usbif_n[DomainAonSel];
  assign rst_en_o.rst_usbif[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_usbif (
    .clk_i(clk_usb_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[USBIF]),
    .q_o(rst_usbif_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_usbif_mux (
    .clk0_i(rst_usbif_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[17] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_usbif_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_usbif_domain_0 (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usbif_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_usbif[Domain0Sel])
  );
  // Generating resets for i2c0
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_i2c0_n;
  assign rst_i2c0_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_i2c0_n[DomainAonSel] = rst_i2c0_n[DomainAonSel];
  assign rst_en_o.rst_i2c0[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_i2c0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[I2C0]),
    .q_o(rst_i2c0_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_i2c0_mux (
    .clk0_i(rst_i2c0_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[18] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_i2c0_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_i2c0_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_i2c0_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_i2c0[Domain0Sel])
  );
  // Generating resets for i2c1
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_i2c1_n;
  assign rst_i2c1_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_i2c1_n[DomainAonSel] = rst_i2c1_n[DomainAonSel];
  assign rst_en_o.rst_i2c1[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_i2c1 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[I2C1]),
    .q_o(rst_i2c1_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_i2c1_mux (
    .clk0_i(rst_i2c1_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[19] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_i2c1_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_i2c1_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_i2c1_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_i2c1[Domain0Sel])
  );
  // Generating resets for i2c2
  // Power Domains: ['0']
  // Shadowed: False
  logic [PowerDomains-1:0] rst_i2c2_n;
  assign rst_i2c2_n[DomainAonSel] = 1'b0;
  assign resets_o.rst_i2c2_n[DomainAonSel] = rst_i2c2_n[DomainAonSel];
  assign rst_en_o.rst_i2c2[DomainAonSel] = lc_ctrl_pkg::On;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_0_i2c2 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_sys_src_n[Domain0Sel]),
    .d_i(sw_rst_ctrl_n[I2C2]),
    .q_o(rst_i2c2_n[Domain0Sel])
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_0_i2c2_mux (
    .clk0_i(rst_i2c2_n[Domain0Sel]),
    .clk1_i(scan_rst_ni),
    .sel_i(leaf_rst_scanmode[20] == lc_ctrl_pkg::On),
    .clk_o(resets_o.rst_i2c2_n[Domain0Sel])
  );

  // reset asserted indication for alert handler
  prim_lc_sender #(
    .ResetValueIsOn(1)
  ) u_prim_lc_sender_i2c2_domain_0 (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_i2c2_n[Domain0Sel]),
    .lc_en_i(lc_ctrl_pkg::Off),
    .lc_en_o(rst_en_o.rst_i2c2[Domain0Sel])
  );

  ////////////////////////////////////////////////////
  // Reset info construction                        //
  ////////////////////////////////////////////////////

  logic rst_hw_req;
  logic rst_low_power;
  logic rst_ndm;
  logic rst_cpu_nq;
  logic first_reset;
  logic pwrmgr_rst_req;

  // there is a valid reset request from pwrmgr
  assign pwrmgr_rst_req = |pwr_i.rst_lc_req | |pwr_i.rst_sys_req;

  // The qualification of first reset below could technically be POR as well.
  // However, that would enforce software to clear POR upon cold power up.  While that is
  // the most likely outcome anyways, hardware should not require that.
  assign rst_hw_req    = ~first_reset & pwrmgr_rst_req &
                         (pwr_i.reset_cause == pwrmgr_pkg::HwReq);
  assign rst_ndm       = ~first_reset & ndm_req_valid;
  assign rst_low_power = ~first_reset & pwrmgr_rst_req &
                         (pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry);

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_cpu_reset_synced (
    .clk_i,
    .rst_ni,
    .d_i(rst_cpu_n_i),
    .q_o(rst_cpu_nq)
  );

  // first reset is a flag that blocks reset recording until first de-assertion
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      first_reset <= 1'b1;
    end else if (rst_cpu_nq) begin
      first_reset <= 1'b0;
    end
  end

  // Only sw is allowed to clear a reset reason, hw is only allowed to set it.
  assign hw2reg.reset_info.low_power_exit.d  = 1'b1;
  assign hw2reg.reset_info.low_power_exit.de = rst_low_power;

  assign hw2reg.reset_info.ndm_reset.d  = 1'b1;
  assign hw2reg.reset_info.ndm_reset.de = rst_ndm;

  // HW reset requests most likely will be multi-bit, so OR in whatever reasons
  // that are already set.
  assign hw2reg.reset_info.hw_req.d  = pwr_i.rstreqs | reg2hw.reset_info.hw_req.q;
  assign hw2reg.reset_info.hw_req.de = rst_hw_req;

  ////////////////////////////////////////////////////
  // Crash info capture                             //
  ////////////////////////////////////////////////////

  logic dump_capture;
  assign dump_capture =  rst_hw_req | rst_ndm | rst_low_power;

  // halt dump capture once we hit particular conditions
  logic dump_capture_halt;
  assign dump_capture_halt = rst_hw_req;

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(alert_pkg::alert_crashdump_t))
  ) u_alert_info (
    .clk_i,
    .rst_ni,
    .dump_i(alert_dump_i),
    .dump_capture_i(dump_capture & reg2hw.alert_info_ctrl.en.q),
    .slot_sel_i(reg2hw.alert_info_ctrl.index.q),
    .slots_cnt_o(hw2reg.alert_info_attr.d),
    .slot_o(hw2reg.alert_info.d)
  );

  rstmgr_crash_info #(
    .CrashDumpWidth($bits(ibex_pkg::crash_dump_t))
  ) u_cpu_info (
    .clk_i,
    .rst_ni,
    .dump_i(cpu_dump_i),
    .dump_capture_i(dump_capture & reg2hw.cpu_info_ctrl.en.q),
    .slot_sel_i(reg2hw.cpu_info_ctrl.index.q),
    .slots_cnt_o(hw2reg.cpu_info_attr.d),
    .slot_o(hw2reg.cpu_info.d)
  );

  // once dump is captured, no more information is captured until
  // re-eanbled by software.
  assign hw2reg.alert_info_ctrl.en.d  = 1'b0;
  assign hw2reg.alert_info_ctrl.en.de = dump_capture_halt;
  assign hw2reg.cpu_info_ctrl.en.d  = 1'b0;
  assign hw2reg.cpu_info_ctrl.en.de = dump_capture_halt;

  ////////////////////////////////////////////////////
  // Exported resets                                //
  ////////////////////////////////////////////////////




  ////////////////////////////////////////////////////
  // Assertions                                     //
  ////////////////////////////////////////////////////

  `ASSERT_INIT(ParameterMatch_A, NumHwResets == pwrmgr_pkg::TotalResetWidth)

  // when upstream resets, downstream must also reset

  // output known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A,    tl_o.d_valid  )
  `ASSERT_KNOWN(TlAReadyKnownO_A,    tl_o.a_ready  )
  `ASSERT_KNOWN(AlertsKnownO_A,      alert_tx_o    )
  `ASSERT_KNOWN(PwrKnownO_A,         pwr_o         )
  `ASSERT_KNOWN(ResetsKnownO_A,      resets_o      )
  `ASSERT_KNOWN(RstEnKnownO_A,       rst_en_o      )

endmodule // rstmgr
