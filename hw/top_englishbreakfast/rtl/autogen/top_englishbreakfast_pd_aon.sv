// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
//                -o hw/top_englishbreakfast/

`include "prim_assert.sv"

module top_englishbreakfast_pd_aon #(
  // TODO Manual parameters for pwrmgr
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
  // Auto-inferred parameters
  // parameters for pwrmgr_aon
  // parameters for rstmgr_aon
  parameter bit SecRstmgrAonCheck = 0,
  parameter int SecRstmgrAonMaxSyncDelay = 2
  // parameters for clkmgr_aon
  // parameters for aon_timer_aon
) (
  // Inter-module Signal External type
  input  pwrmgr_pkg::pwr_nvm_t       pwrmgr_aon_pwr_nvm_i,
  output logic       pwrmgr_aon_strap_o,
  output logic       pwrmgr_aon_low_power_o,
  output lc_ctrl_pkg::lc_tx_t       pwrmgr_aon_fetch_en_o,
  input  prim_mubi_pkg::mubi4_t       clkmgr_aon_idle_i,
  input  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump_i,
  input  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr_i,
  input  logic [1:0] pwrmgr_aon_wakeups_i,
  input  tlul_pkg::tl_h2d_t       pwrmgr_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       pwrmgr_aon_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       rstmgr_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       rstmgr_aon_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       clkmgr_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       clkmgr_aon_tl_rsp_o,
  output clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks_o,
  output clkmgr_pkg::clkmgr_cg_en_t       clkmgr_aon_cg_en_o,
  output prim_mubi_pkg::mubi4_t       clk_main_jitter_en_o,
  output prim_mubi_pkg::mubi4_t       hi_speed_sel_o,
  input  prim_mubi_pkg::mubi4_t       div_step_down_req_i,
  output prim_mubi_pkg::mubi4_t       all_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       all_clk_byp_ack_i,
  output prim_mubi_pkg::mubi4_t       io_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       io_clk_byp_ack_i,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_ast_rsp_i,
  input  logic [1:0] por_n_i,
  output rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets_o,
  output rstmgr_pkg::rstmgr_rst_en_t       rstmgr_aon_rst_en_o,

  // Interrupts to PLIC rv_plic in power domain Main
  output logic [2:0] intr_vector_o,

  // Outgoing alerts for group englishbreakfast
  output prim_alert_pkg::alert_tx_t [top_englishbreakfast_pkg::NOutgoingAlertsEnglishbreakfastPdAon-1:0] outgoing_alert_englishbreakfast_tx_o,
  input  prim_alert_pkg::alert_rx_t [top_englishbreakfast_pkg::NOutgoingAlertsEnglishbreakfastPdAon-1:0] outgoing_alert_englishbreakfast_rx_i,
  output prim_mubi_pkg::mubi4_t     [top_englishbreakfast_pkg::NOutgoingLpgsEnglishbreakfast-1:0]   outgoing_lpg_cg_en_englishbreakfast_o,
  output prim_mubi_pkg::mubi4_t     [top_englishbreakfast_pkg::NOutgoingLpgsEnglishbreakfast-1:0]   outgoing_lpg_rst_en_englishbreakfast_o,

  // Externally supplied clocks
  input clk_main_i,
  input clk_io_i,
  input clk_usb_i,
  input clk_aon_i,


  // Manual DFT signals
  input                        scan_rst_ni, // reset used for test mode
  input prim_mubi_pkg::mubi4_t scanmode_i   // lc_ctrl_pkg::On for Scan
);

  import top_englishbreakfast_pkg::*;
  // Compile-time random constants
  import top_englishbreakfast_rnd_cnst_pkg::*;

  // Local Parameters

  // Signals


  // Interrupt source list
  logic intr_pwrmgr_aon_wakeup;
  logic intr_aon_timer_aon_wkup_timer_expired;
  logic intr_aon_timer_aon_wdog_timer_bark;


  // Define inter-module signals
  pwrmgr_pkg::pwr_rst_req_t       pwrmgr_aon_pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t       pwrmgr_aon_pwr_rst_rsp;
  pwrmgr_pkg::pwr_clk_req_t       pwrmgr_aon_pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t       pwrmgr_aon_pwr_clk_rsp;
  logic       pwrmgr_aon_low_power;
  prim_mubi_pkg::mubi4_t       rstmgr_aon_sw_rst_req;
  logic [2:0] pwrmgr_aon_wakeups;
  logic       pwrmgr_aon_rstreqs;
  clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks;
  clkmgr_pkg::clkmgr_cg_en_t       clkmgr_aon_cg_en;
  rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets;
  rstmgr_pkg::rstmgr_rst_en_t       rstmgr_aon_rst_en;

  // Create mixed connections to ports
  assign pwrmgr_aon_low_power_o = pwrmgr_aon_low_power;
  assign pwrmgr_aon_wakeups[0] = pwrmgr_aon_wakeups_i[0];
  assign pwrmgr_aon_wakeups[1] = pwrmgr_aon_wakeups_i[1];
  assign clkmgr_aon_clocks_o = clkmgr_aon_clocks;
  assign clkmgr_aon_cg_en_o = clkmgr_aon_cg_en;
  assign rstmgr_aon_resets_o = rstmgr_aon_resets;
  assign rstmgr_aon_rst_en_o = rstmgr_aon_rst_en;


  // Outgoing LPGs for alert group englishbreakfast
  // peri_lc_io_div4_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[0] = clkmgr_aon_cg_en.io_div4_peri;
  assign outgoing_lpg_rst_en_englishbreakfast_o[0] = rstmgr_aon_rst_en.lc_io_div4[rstmgr_pkg::DomainMainSel];
  // peri_sys_io_div4_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[1] = clkmgr_aon_cg_en.io_div4_peri;
  assign outgoing_lpg_rst_en_englishbreakfast_o[1] = rstmgr_aon_rst_en.sys_io_div4[rstmgr_pkg::DomainMainSel];
  // peri_spi_device_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[2] = clkmgr_aon_cg_en.io_div4_peri;
  assign outgoing_lpg_rst_en_englishbreakfast_o[2] = rstmgr_aon_rst_en.spi_device[rstmgr_pkg::DomainMainSel];
  // peri_spi_host0_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[3] = clkmgr_aon_cg_en.io_peri;
  assign outgoing_lpg_rst_en_englishbreakfast_o[3] = rstmgr_aon_rst_en.spi_host0[rstmgr_pkg::DomainMainSel];
  // timers_sys_io_div4_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[4] = clkmgr_aon_cg_en.io_div4_timers;
  assign outgoing_lpg_rst_en_englishbreakfast_o[4] = rstmgr_aon_rst_en.sys_io_div4[rstmgr_pkg::DomainMainSel];
  // peri_usb_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[5] = clkmgr_aon_cg_en.usb_peri;
  assign outgoing_lpg_rst_en_englishbreakfast_o[5] = rstmgr_aon_rst_en.usb[rstmgr_pkg::DomainMainSel];
  // powerup_por_io_div4_Aon
  assign outgoing_lpg_cg_en_englishbreakfast_o[6] = clkmgr_aon_cg_en.io_div4_powerup;
  assign outgoing_lpg_rst_en_englishbreakfast_o[6] = rstmgr_aon_rst_en.por_io_div4[rstmgr_pkg::DomainAonSel];
  // powerup_lc_io_div4_Aon
  assign outgoing_lpg_cg_en_englishbreakfast_o[7] = clkmgr_aon_cg_en.io_div4_powerup;
  assign outgoing_lpg_rst_en_englishbreakfast_o[7] = rstmgr_aon_rst_en.lc_io_div4[rstmgr_pkg::DomainAonSel];
  // timers_sys_io_div4_Aon
  assign outgoing_lpg_cg_en_englishbreakfast_o[8] = clkmgr_aon_cg_en.io_div4_timers;
  assign outgoing_lpg_rst_en_englishbreakfast_o[8] = rstmgr_aon_rst_en.sys_io_div4[rstmgr_pkg::DomainAonSel];
  // infra_lc_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[9] = clkmgr_aon_cg_en.main_infra;
  assign outgoing_lpg_rst_en_englishbreakfast_o[9] = rstmgr_aon_rst_en.lc[rstmgr_pkg::DomainMainSel];
  // secure_sys_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[10] = clkmgr_aon_cg_en.main_secure;
  assign outgoing_lpg_rst_en_englishbreakfast_o[10] = rstmgr_aon_rst_en.sys[rstmgr_pkg::DomainMainSel];
  // aes_trans_sys_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[11] = clkmgr_aon_cg_en.main_aes;
  assign outgoing_lpg_rst_en_englishbreakfast_o[11] = rstmgr_aon_rst_en.sys[rstmgr_pkg::DomainMainSel];
  // infra_sys_Main
  assign outgoing_lpg_cg_en_englishbreakfast_o[12] = clkmgr_aon_cg_en.main_infra;
  assign outgoing_lpg_rst_en_englishbreakfast_o[12] = rstmgr_aon_rst_en.sys[rstmgr_pkg::DomainMainSel];

  // Instantiation of IPs
  pwrmgr #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[7]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .EscNumSeverities(4),
    .EscPingCountWidth(16)
  ) u_pwrmgr_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .clk_slow_i(clkmgr_aon_clocks.clk_aon_powerup),
    .clk_lc_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .clk_esc_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .rst_ni(rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_lc_ni(rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_esc_ni(rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_main_ni(rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_slow_ni(rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_wakeup_o(intr_pwrmgr_aon_wakeup),

    // External alert group "englishbreakfast" [7]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[0]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[0]),

    // Inter-module signals
    .pwr_ast_o(pwrmgr_ast_req_o),
    .pwr_ast_i(pwrmgr_ast_rsp_i),
    .pwr_rst_o(pwrmgr_aon_pwr_rst_req),
    .pwr_rst_i(pwrmgr_aon_pwr_rst_rsp),
    .pwr_clk_o(pwrmgr_aon_pwr_clk_req),
    .pwr_clk_i(pwrmgr_aon_pwr_clk_rsp),
    .pwr_otp_o(),
    .pwr_otp_i(pwrmgr_pkg::PWR_OTP_RSP_DEFAULT),
    .pwr_lc_o(),
    .pwr_lc_i(lc_ctrl_pkg::PWR_LC_RSP_DEFAULT),
    .pwr_nvm_i(pwrmgr_aon_pwr_nvm_i),
    .esc_rst_tx_i(prim_esc_pkg::ESC_TX_DEFAULT),
    .esc_rst_rx_o(),
    .pwr_cpu_i(rv_core_ibex_pwrmgr_i),
    .wakeups_i(pwrmgr_aon_wakeups),
    .rstreqs_i(pwrmgr_aon_rstreqs),
    .ndmreset_req_i('0),
    .strap_o(pwrmgr_aon_strap_o),
    .low_power_o(pwrmgr_aon_low_power),
    .rom_ctrl_i(rom_ctrl_pkg::PWRMGR_DATA_DEFAULT),
    .fetch_en_o(pwrmgr_aon_fetch_en_o),
    .lc_dft_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_hw_debug_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .sw_rst_req_i(rstmgr_aon_sw_rst_req),
    .tl_i(pwrmgr_aon_tl_req_i),
    .tl_o(pwrmgr_aon_tl_rsp_o)
  );

  rstmgr #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[9:8]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .SecCheck(SecRstmgrAonCheck),
    .SecMaxSyncDelay(SecRstmgrAonMaxSyncDelay)
  ) u_rstmgr_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .clk_por_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .clk_aon_i(clkmgr_aon_clocks.clk_aon_powerup),
    .clk_main_i(clkmgr_aon_clocks.clk_main_powerup),
    .clk_io_i(clkmgr_aon_clocks.clk_io_powerup),
    .clk_usb_i(clkmgr_aon_clocks.clk_usb_powerup),
    .clk_io_div2_i(clkmgr_aon_clocks.clk_io_div2_powerup),
    .clk_io_div4_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .rst_ni(rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_por_ni(rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i,
    .scan_rst_ni,

    // External alert group "englishbreakfast" [8]: fatal_fault
    // External alert group "englishbreakfast" [9]: fatal_cnsty_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[2:1]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[2:1]),

    // Inter-module signals
    .por_n_i(por_n_i),
    .pwr_i(pwrmgr_aon_pwr_rst_req),
    .pwr_o(pwrmgr_aon_pwr_rst_rsp),
    .resets_o(rstmgr_aon_resets),
    .rst_en_o(rstmgr_aon_rst_en),
    .alert_dump_i(alert_handler_pkg::ALERT_CRASHDUMP_DEFAULT),
    .cpu_dump_i(rv_core_ibex_crash_dump_i),
    .sw_rst_req_o(rstmgr_aon_sw_rst_req),
    .tl_i(rstmgr_aon_tl_req_i),
    .tl_o(rstmgr_aon_tl_rsp_o)
  );

  clkmgr #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[11:10]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_clkmgr_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_div4_powerup),
    .clk_main_i(clk_main_i),
    .clk_io_i(clk_io_i),
    .clk_usb_i(clk_usb_i),
    .clk_aon_i(clk_aon_i),
    .rst_shadowed_ni(rstmgr_aon_resets.rst_por_io_div4_shadowed_n[rstmgr_pkg::DomainAonSel]),
    .rst_ni(rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_div2_ni(rstmgr_aon_resets.rst_por_io_div2_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_div4_ni(rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_main_ni(rstmgr_aon_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
    .rst_usb_ni(rstmgr_aon_resets.rst_por_usb_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_ni(rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_div2_ni(rstmgr_aon_resets.rst_por_io_div2_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_div4_ni(rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_main_ni(rstmgr_aon_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_usb_ni(rstmgr_aon_resets.rst_por_usb_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i,

    // External alert group "englishbreakfast" [10]: recov_fault
    // External alert group "englishbreakfast" [11]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[4:3]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[4:3]),

    // Inter-module signals
    .clocks_o(clkmgr_aon_clocks),
    .cg_en_o(clkmgr_aon_cg_en),
    .lc_hw_debug_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .io_clk_byp_req_o(io_clk_byp_req_o),
    .io_clk_byp_ack_i(io_clk_byp_ack_i),
    .all_clk_byp_req_o(all_clk_byp_req_o),
    .all_clk_byp_ack_i(all_clk_byp_ack_i),
    .hi_speed_sel_o(hi_speed_sel_o),
    .div_step_down_req_i(div_step_down_req_i),
    .lc_clk_byp_req_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_clk_byp_ack_o(),
    .jitter_en_o(clk_main_jitter_en_o),
    .pwr_i(pwrmgr_aon_pwr_clk_req),
    .pwr_o(pwrmgr_aon_pwr_clk_rsp),
    .idle_i(clkmgr_aon_idle_i),
    .calib_rdy_i(prim_mubi_pkg::MuBi4True),
    .tl_i(clkmgr_aon_tl_req_i),
    .tl_o(clkmgr_aon_tl_rsp_o)
  );

  aon_timer #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[13]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_aon_timer_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_div4_timers),
    .clk_aon_i(clkmgr_aon_clocks.clk_aon_timers),
    .rst_ni(rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_wkup_timer_expired_o(intr_aon_timer_aon_wkup_timer_expired),
    .intr_wdog_timer_bark_o   (intr_aon_timer_aon_wdog_timer_bark),

    // External alert group "englishbreakfast" [13]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[5]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[5]),

    // Inter-module signals
    .nmi_wdog_timer_bark_o(),
    .wkup_req_o(pwrmgr_aon_wakeups[2]),
    .aon_timer_rst_req_o(pwrmgr_aon_rstreqs),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .sleep_mode_i(pwrmgr_aon_low_power),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(tlul_pkg::TL_H2D_DEFAULT),
    .tl_o()
  );


  // Interrupt vector to PLIC rv_plic in power domain Main
  assign intr_vector_o = {
    intr_aon_timer_aon_wdog_timer_bark,
    intr_aon_timer_aon_wkup_timer_expired,
    intr_pwrmgr_aon_wakeup
  };



  // Make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_main_i, 0)

endmodule
