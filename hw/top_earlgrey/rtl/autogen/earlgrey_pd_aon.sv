// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/

`include "prim_assert.sv"

module earlgrey_pd_aon #(
  // TODO Manual parameters for pwrmgr
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
  // Auto-inferred parameters
  // parameters for rstmgr
  parameter bit SecRstmgrCheck = 1'b1,
  parameter int SecRstmgrMaxSyncDelay = 2,
  // parameters for ast
  parameter int unsigned AstUsbCalibWidth = 20,
  parameter int unsigned AstPad2AstInWidth = 8,
  // parameters for sram_ctrl_ret
  parameter int SramCtrlRetInstSize = 4096,
  parameter int SramCtrlRetNumRamInst = 1,
  parameter bit SramCtrlRetInstrExec = 0,
  parameter int SramCtrlRetNumPrinceRoundsHalf = 3,
  parameter int SramCtrlRetNumAddrScrRounds = 2,
  parameter bit SramCtrlRetEccCorrection = 0
) (
  // Inter-module Signal External type
  output ast_pkg::ast_obs_ctrl_t       ast_obs_ctrl_o,
  output prim_mubi_pkg::mubi4_t       ast_clk_src_sys_jen_o,
  input  prim_mubi_pkg::mubi4_t       ast_init_done_i,
  input  logic       spi_device_sck_monitor_i,
  input  logic       usbdev_usb_ref_pulse_i,
  input  logic       usbdev_usb_ref_val_i,
  input  pinmux_pkg::dft_strap_test_req_t       pinmux_dft_strap_test_i,
  output prim_mubi_pkg::mubi4_t       clkmgr_all_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       clkmgr_all_clk_byp_ack_i,
  output prim_mubi_pkg::mubi4_t       clkmgr_io_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       clkmgr_io_clk_byp_ack_i,
  output prim_mubi_pkg::mubi4_t       clkmgr_hi_speed_sel_o,
  input  prim_mubi_pkg::mubi4_t       clkmgr_div_step_down_req_i,
  input  alert_handler_pkg::alert_crashdump_t       alert_handler_crashdump_i,
  output prim_esc_pkg::esc_rx_t       alert_handler_esc_rx_o,
  input  prim_esc_pkg::esc_tx_t       alert_handler_esc_tx_i,
  output logic       aon_timer_nmi_wdog_timer_bark_o,
  output otp_ctrl_pkg::sram_otp_key_req_t       otp_ctrl_sram_otp_key_req_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t       otp_ctrl_sram_otp_key_rsp_i,
  input  pwrmgr_pkg::pwr_nvm_t       pwrmgr_pwr_nvm_i,
  output pwrmgr_pkg::pwr_otp_req_t       pwrmgr_pwr_otp_req_o,
  input  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_pwr_otp_rsp_i,
  output lc_ctrl_pkg::pwr_lc_req_t       pwrmgr_pwr_lc_req_o,
  input  lc_ctrl_pkg::pwr_lc_rsp_t       pwrmgr_pwr_lc_rsp_i,
  output logic       pwrmgr_strap_o,
  output logic       pwrmgr_low_power_o,
  output lc_ctrl_pkg::lc_tx_t       pwrmgr_fetch_en_o,
  input  rom_ctrl_pkg::pwrmgr_data_t       rom_ctrl_pwrmgr_data_i,
  input  prim_mubi_pkg::mubi4_t [3:0] clkmgr_idle_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_req_i,
  output lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_ack_o,
  input  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump_i,
  input  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr_i,
  input  logic       rv_dm_ndmreset_req_i,
  input  logic [1:0] pwrmgr_wakeups_i,
  output ast_intraip_pkg::s2p_t       ast_intraip_s2p_o,
  input  ast_intraip_pkg::p2s_t       ast_intraip_p2s_i,
  input  tlul_pkg::tl_h2d_t       pwrmgr_tl_req_i,
  output tlul_pkg::tl_d2h_t       pwrmgr_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       rstmgr_tl_req_i,
  output tlul_pkg::tl_d2h_t       rstmgr_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       clkmgr_tl_req_i,
  output tlul_pkg::tl_d2h_t       clkmgr_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       sensor_ctrl_tl_req_i,
  output tlul_pkg::tl_d2h_t       sensor_ctrl_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       sram_ctrl_ret_regs_tl_req_i,
  output tlul_pkg::tl_d2h_t       sram_ctrl_ret_regs_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       sram_ctrl_ret_ram_tl_req_i,
  output tlul_pkg::tl_d2h_t       sram_ctrl_ret_ram_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       aon_timer_tl_req_i,
  output tlul_pkg::tl_d2h_t       aon_timer_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       sysrst_ctrl_tl_req_i,
  output tlul_pkg::tl_d2h_t       sysrst_ctrl_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       adc_ctrl_tl_req_i,
  output tlul_pkg::tl_d2h_t       adc_ctrl_tl_rsp_o,
  input  logic       manual_in_por_n_i,
  output prim_mubi_pkg::mubi4_t       scanmode_o,
  output logic       scan_en_o,
  output logic       scan_rst_n_o,
  output logic [AstUsbCalibWidth-1:0] usb_io_pu_cal_o,
  input  logic [AstPad2AstInWidth-1:0] padmux2ast_i,
  output logic [3:0] mux_iob_sel_o,
  input  ast_pkg::ast_vx_supp_t       ast_vx_supp_i,
  input  ast_pkg::ast_obs_bus_t       ast_obs_i,
  input  ast_pkg::awire_t       ast_adc_a0_a_i,
  input  ast_pkg::awire_t       ast_adc_a1_a_i,
  output ast_pkg::awire_t       ast2pad_t0_a_o,
  output ast_pkg::awire_t       ast2pad_t1_a_o,
  input  ast_pkg::clks_osc_byp_t       clk_osc_byp_pd_aon_i,
  output ast_pkg::ast_pwst_t       ast_pwst_h_o,
  output prim_pad_wrapper_pkg::pad_attr_t [3:0] sensor_ctrl_manual_pad_attr_o,
  output logic       cio_sysrst_ctrl_ec_rst_l_d2p_o,
  output logic       cio_sysrst_ctrl_ec_rst_l_en_d2p_o,
  input  logic       cio_sysrst_ctrl_ec_rst_l_p2d_i,
  output logic       cio_sysrst_ctrl_flash_wp_l_d2p_o,
  output logic       cio_sysrst_ctrl_flash_wp_l_en_d2p_o,
  input  logic       cio_sysrst_ctrl_flash_wp_l_p2d_i,
  input  logic       cio_sysrst_ctrl_ac_present_p2d_i,
  input  logic       cio_sysrst_ctrl_key0_in_p2d_i,
  input  logic       cio_sysrst_ctrl_key1_in_p2d_i,
  input  logic       cio_sysrst_ctrl_key2_in_p2d_i,
  input  logic       cio_sysrst_ctrl_pwrb_in_p2d_i,
  input  logic       cio_sysrst_ctrl_lid_open_p2d_i,
  output logic       cio_sysrst_ctrl_bat_disable_d2p_o,
  output logic       cio_sysrst_ctrl_bat_disable_en_d2p_o,
  output logic       cio_sysrst_ctrl_key0_out_d2p_o,
  output logic       cio_sysrst_ctrl_key0_out_en_d2p_o,
  output logic       cio_sysrst_ctrl_key1_out_d2p_o,
  output logic       cio_sysrst_ctrl_key1_out_en_d2p_o,
  output logic       cio_sysrst_ctrl_key2_out_d2p_o,
  output logic       cio_sysrst_ctrl_key2_out_en_d2p_o,
  output logic       cio_sysrst_ctrl_pwrb_out_d2p_o,
  output logic       cio_sysrst_ctrl_pwrb_out_en_d2p_o,
  output logic       cio_sysrst_ctrl_z3_wakeup_d2p_o,
  output logic       cio_sysrst_ctrl_z3_wakeup_en_d2p_o,
  output logic [8:0] cio_sensor_ctrl_ast_debug_out_d2p_o,
  output logic [8:0] cio_sensor_ctrl_ast_debug_out_en_d2p_o,
  input  logic       ast_clk_src_sys_i,
  input  logic       ast_clk_src_io_i,
  input  logic       ast_clk_src_usb_i,

  // Interrupts to PLIC rv_plic in power domain Main
  output logic [6:0] intr_vector_o,

  // Alerts to power domain Main
  input  prim_alert_pkg::alert_rx_t [10:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [10:0] alert_tx_o,

  // Clocks from clkmgr to other domains
  output clkmgr_pkg::clkmgr_out_t    clkmgr_clocks_o,
  output clkmgr_pkg::clkmgr_cg_en_t  clkmgr_cg_en_o,

  // Resets from rstmgr to other domains
  output rstmgr_pkg::rstmgr_out_t    rstmgr_resets_o,
  output rstmgr_pkg::rstmgr_rst_en_t rstmgr_rst_en_o,

  // Unmanaged external clocks
  input                        clk_ast_ext_i,
  input prim_mubi_pkg::mubi4_t cg_en_ast_ext_i

);

  import top_earlgrey_pkg::*;
  // Compile-time random constants
  import top_earlgrey_rnd_cnst_pkg::*;

  // Local Parameters
  // local parameters for ast
  localparam int unsigned AstAst2PadOutWidth = 9;
  // local parameters for sram_ctrl_ret
  localparam int SramCtrlRetOutstanding = 2;

  // Signals


  // Interrupt source list
  logic intr_pwrmgr_wakeup;
  logic intr_sysrst_ctrl_event_detected;
  logic intr_adc_ctrl_match_pending;
  logic intr_aon_timer_wkup_timer_expired;
  logic intr_aon_timer_wdog_timer_bark;
  logic intr_sensor_ctrl_io_status_change;
  logic intr_sensor_ctrl_init_status_change;

  // Alert list


  // Define inter-module signals
  ast_pkg::adc_ast_req_t       ast_adc_req;
  ast_pkg::adc_ast_rsp_t       ast_adc_rsp;
  clkmgr_pkg::clkmgr_out_t       ast_sns_clks;
  rstmgr_pkg::rstmgr_out_t       ast_sns_rsts;
  logic [AstAst2PadOutWidth-1:0] ast_ast2padmux;
  ast_pkg::ast_status_t       ast_io_pwr_st;
  prim_mubi_pkg::mubi4_t       clkmgr_all_clk_byp_req;
  prim_mubi_pkg::mubi4_t       clkmgr_io_clk_byp_req;
  prim_mubi_pkg::mubi4_t       clkmgr_hi_speed_sel;
  ast_pkg::ast_alert_req_t       sensor_ctrl_ast_alert_req;
  ast_pkg::ast_alert_rsp_t       sensor_ctrl_ast_alert_rsp;
  pwrmgr_pkg::pwr_ast_req_t       pwrmgr_pwr_ast_req;
  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_pwr_ast_rsp;
  pwrmgr_pkg::pwr_rst_req_t       pwrmgr_pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t       pwrmgr_pwr_rst_rsp;
  pwrmgr_pkg::pwr_clk_req_t       pwrmgr_pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t       pwrmgr_pwr_clk_rsp;
  logic       pwrmgr_low_power;
  prim_mubi_pkg::mubi4_t       rstmgr_sw_rst_req;
  logic [1:0] rstmgr_por_n;
  logic [5:0] pwrmgr_wakeups;
  logic [1:0] pwrmgr_rstreqs;
  clkmgr_pkg::clkmgr_out_t       clkmgr_clocks;
  logic       ast_clk_src_aon;
  ast_pkg::clks_osc_byp_t       ast_clk_osc_byp;
  ast_pkg::ast_mem_cfg_secondary_req_t       ast_mem_cfg_req;
  ast_pkg::ast_mem_cfg_secondary_rsp_t       ast_mem_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t [SramCtrlRetNumRamInst-1:0] sram_ctrl_ret_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlRetNumRamInst-1:0] sram_ctrl_ret_ram_cfg_rsp;
  clkmgr_pkg::clkmgr_cg_en_t       clkmgr_cg_en;
  rstmgr_pkg::rstmgr_out_t       rstmgr_resets;
  rstmgr_pkg::rstmgr_rst_en_t       rstmgr_rst_en;

  // Create mixed connections to ports
  assign clkmgr_all_clk_byp_req_o = clkmgr_all_clk_byp_req;
  assign clkmgr_io_clk_byp_req_o = clkmgr_io_clk_byp_req;
  assign clkmgr_hi_speed_sel_o = clkmgr_hi_speed_sel;
  assign pwrmgr_low_power_o = pwrmgr_low_power;
  assign pwrmgr_wakeups[2] = pwrmgr_wakeups_i[0];
  assign pwrmgr_wakeups[3] = pwrmgr_wakeups_i[1];
  assign ast_clk_osc_byp = clk_osc_byp_pd_aon_i;




  // Instantiation of IPs
  pwrmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[21]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .EscNumSeverities(AlertHandlerEscNumSeverities),
    .EscPingCountWidth(AlertHandlerEscPingCountWidth)
  ) u_pwrmgr (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_powerup),
    .clk_slow_i(clkmgr_clocks.clk_aon_powerup),
    .clk_lc_i(clkmgr_clocks.clk_io_div4_powerup),
    .clk_esc_i(clkmgr_clocks.clk_io_div4_secure),
    .rst_ni(rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_main_ni(rstmgr_resets.rst_por_aon_n[rstmgr_pkg::DomainMainSel]),
    .rst_lc_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_esc_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_slow_ni(rstmgr_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_wakeup_o(intr_pwrmgr_wakeup),

    // alert_handler[21]: fatal_fault
    .alert_tx_o(alert_tx_o[0]),
    .alert_rx_i(alert_rx_i[0]),

    // Inter-module signals
    .pwr_ast_o(pwrmgr_pwr_ast_req),
    .pwr_ast_i(pwrmgr_pwr_ast_rsp),
    .pwr_rst_o(pwrmgr_pwr_rst_req),
    .pwr_rst_i(pwrmgr_pwr_rst_rsp),
    .pwr_clk_o(pwrmgr_pwr_clk_req),
    .pwr_clk_i(pwrmgr_pwr_clk_rsp),
    .pwr_otp_o(pwrmgr_pwr_otp_req_o),
    .pwr_otp_i(pwrmgr_pwr_otp_rsp_i),
    .pwr_lc_o(pwrmgr_pwr_lc_req_o),
    .pwr_lc_i(pwrmgr_pwr_lc_rsp_i),
    .pwr_nvm_i(pwrmgr_pwr_nvm_i),
    .esc_rst_tx_i(alert_handler_esc_tx_i),
    .esc_rst_rx_o(alert_handler_esc_rx_o),
    .pwr_cpu_i(rv_core_ibex_pwrmgr_i),
    .wakeups_i(pwrmgr_wakeups),
    .rstreqs_i(pwrmgr_rstreqs),
    .ndmreset_req_i(rv_dm_ndmreset_req_i),
    .strap_o(pwrmgr_strap_o),
    .low_power_o(pwrmgr_low_power),
    .rom_ctrl_i(rom_ctrl_pwrmgr_data_i),
    .fetch_en_o(pwrmgr_fetch_en_o),
    .lc_dft_en_i(lc_ctrl_lc_dft_en_i),
    .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en_i),
    .sw_rst_req_i(rstmgr_sw_rst_req),
    .tl_i(pwrmgr_tl_req_i),
    .tl_o(pwrmgr_tl_rsp_o)
  );

  rstmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[23:22]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .SecCheck(SecRstmgrCheck),
    .SecMaxSyncDelay(SecRstmgrMaxSyncDelay)
  ) u_rstmgr (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_powerup),
    .clk_por_i(clkmgr_clocks.clk_io_div4_powerup),
    .clk_aon_i(clkmgr_clocks.clk_aon_powerup),
    .clk_main_i(clkmgr_clocks.clk_main_powerup),
    .clk_io_i(clkmgr_clocks.clk_io_powerup),
    .clk_usb_i(clkmgr_clocks.clk_usb_powerup),
    .clk_io_div2_i(clkmgr_clocks.clk_io_div2_powerup),
    .clk_io_div4_i(clkmgr_clocks.clk_io_div4_powerup),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_por_ni(rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i(scanmode_o),
    .scan_rst_ni(scan_rst_n_o),

    // alert_handler[22]: fatal_fault
    // alert_handler[23]: fatal_cnsty_fault
    .alert_tx_o(alert_tx_o[2:1]),
    .alert_rx_i(alert_rx_i[2:1]),

    // Inter-module signals
    .por_n_i(rstmgr_por_n),
    .pwr_i(pwrmgr_pwr_rst_req),
    .pwr_o(pwrmgr_pwr_rst_rsp),
    .resets_o(rstmgr_resets),
    .rst_en_o(rstmgr_rst_en),
    .alert_dump_i(alert_handler_crashdump_i),
    .cpu_dump_i(rv_core_ibex_crash_dump_i),
    .sw_rst_req_o(rstmgr_sw_rst_req),
    .tl_i(rstmgr_tl_req_i),
    .tl_o(rstmgr_tl_rsp_o)
  );

  clkmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[25:24]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_clkmgr (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_powerup),
    .clk_main_i(ast_clk_src_sys_i),
    .clk_io_i(ast_clk_src_io_i),
    .clk_usb_i(ast_clk_src_usb_i),
    .clk_aon_i(ast_clk_src_aon),
    .rst_shadowed_ni(rstmgr_resets.rst_lc_io_div4_shadowed_n[rstmgr_pkg::DomainAonSel]),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_ni(rstmgr_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_div2_ni(rstmgr_resets.rst_lc_io_div2_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_div4_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_main_ni(rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainAonSel]),
    .rst_usb_ni(rstmgr_resets.rst_lc_usb_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_ni(rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_ni(rstmgr_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_div2_ni(rstmgr_resets.rst_por_io_div2_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_div4_ni(rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_main_ni(rstmgr_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_usb_ni(rstmgr_resets.rst_por_usb_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i(scanmode_o),

    // alert_handler[24]: recov_fault
    // alert_handler[25]: fatal_fault
    .alert_tx_o(alert_tx_o[4:3]),
    .alert_rx_i(alert_rx_i[4:3]),

    // Inter-module signals
    .clocks_o(clkmgr_clocks),
    .cg_en_o(clkmgr_cg_en),
    .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en_i),
    .io_clk_byp_req_o(clkmgr_io_clk_byp_req),
    .io_clk_byp_ack_i(clkmgr_io_clk_byp_ack_i),
    .all_clk_byp_req_o(clkmgr_all_clk_byp_req),
    .all_clk_byp_ack_i(clkmgr_all_clk_byp_ack_i),
    .hi_speed_sel_o(clkmgr_hi_speed_sel),
    .div_step_down_req_i(clkmgr_div_step_down_req_i),
    .lc_clk_byp_req_i(lc_ctrl_lc_clk_byp_req_i),
    .lc_clk_byp_ack_o(lc_ctrl_lc_clk_byp_ack_o),
    .jitter_en_o(ast_clk_src_sys_jen_o),
    .pwr_i(pwrmgr_pwr_clk_req),
    .pwr_o(pwrmgr_pwr_clk_rsp),
    .idle_i(clkmgr_idle_i),
    .calib_rdy_i(ast_init_done_i),
    .tl_i(clkmgr_tl_req_i),
    .tl_o(clkmgr_tl_rsp_o)
  );

  sysrst_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[26]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_sysrst_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_secure),
    .clk_aon_i(clkmgr_clocks.clk_aon_secure),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_event_detected_o(intr_sysrst_ctrl_event_detected),

    // alert_handler[26]: fatal_fault
    .alert_tx_o(alert_tx_o[5]),
    .alert_rx_i(alert_rx_i[5]),

    // CIO inputs
    .cio_ac_present_i    (cio_sysrst_ctrl_ac_present_p2d_i),
    .cio_key0_in_i       (cio_sysrst_ctrl_key0_in_p2d_i),
    .cio_key1_in_i       (cio_sysrst_ctrl_key1_in_p2d_i),
    .cio_key2_in_i       (cio_sysrst_ctrl_key2_in_p2d_i),
    .cio_pwrb_in_i       (cio_sysrst_ctrl_pwrb_in_p2d_i),
    .cio_lid_open_i      (cio_sysrst_ctrl_lid_open_p2d_i),
    .cio_ec_rst_l_i      (cio_sysrst_ctrl_ec_rst_l_p2d_i),
    .cio_flash_wp_l_i    (cio_sysrst_ctrl_flash_wp_l_p2d_i),

    // CIO outputs
    .cio_bat_disable_o   (cio_sysrst_ctrl_bat_disable_d2p_o),
    .cio_bat_disable_en_o(cio_sysrst_ctrl_bat_disable_en_d2p_o),
    .cio_key0_out_o      (cio_sysrst_ctrl_key0_out_d2p_o),
    .cio_key0_out_en_o   (cio_sysrst_ctrl_key0_out_en_d2p_o),
    .cio_key1_out_o      (cio_sysrst_ctrl_key1_out_d2p_o),
    .cio_key1_out_en_o   (cio_sysrst_ctrl_key1_out_en_d2p_o),
    .cio_key2_out_o      (cio_sysrst_ctrl_key2_out_d2p_o),
    .cio_key2_out_en_o   (cio_sysrst_ctrl_key2_out_en_d2p_o),
    .cio_pwrb_out_o      (cio_sysrst_ctrl_pwrb_out_d2p_o),
    .cio_pwrb_out_en_o   (cio_sysrst_ctrl_pwrb_out_en_d2p_o),
    .cio_z3_wakeup_o     (cio_sysrst_ctrl_z3_wakeup_d2p_o),
    .cio_z3_wakeup_en_o  (cio_sysrst_ctrl_z3_wakeup_en_d2p_o),
    .cio_ec_rst_l_o      (cio_sysrst_ctrl_ec_rst_l_d2p_o),
    .cio_ec_rst_l_en_o   (cio_sysrst_ctrl_ec_rst_l_en_d2p_o),
    .cio_flash_wp_l_o    (cio_sysrst_ctrl_flash_wp_l_d2p_o),
    .cio_flash_wp_l_en_o (cio_sysrst_ctrl_flash_wp_l_en_d2p_o),

    // Inter-module signals
    .wkup_req_o(pwrmgr_wakeups[0]),
    .rst_req_o(pwrmgr_rstreqs[0]),
    .tl_i(sysrst_ctrl_tl_req_i),
    .tl_o(sysrst_ctrl_tl_rsp_o)
  );

  adc_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[27]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_adc_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_peri),
    .clk_aon_i(clkmgr_clocks.clk_aon_peri),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_match_pending_o(intr_adc_ctrl_match_pending),

    // alert_handler[27]: fatal_fault
    .alert_tx_o(alert_tx_o[6]),
    .alert_rx_i(alert_rx_i[6]),

    // Inter-module signals
    .adc_o(ast_adc_req),
    .adc_i(ast_adc_rsp),
    .wkup_req_o(pwrmgr_wakeups[1]),
    .tl_i(adc_ctrl_tl_req_i),
    .tl_o(adc_ctrl_tl_rsp_o)
  );

  aon_timer #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[29]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_aon_timer (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_timers),
    .clk_aon_i(clkmgr_clocks.clk_aon_timers),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_wkup_timer_expired_o(intr_aon_timer_wkup_timer_expired),
    .intr_wdog_timer_bark_o   (intr_aon_timer_wdog_timer_bark),

    // alert_handler[29]: fatal_fault
    .alert_tx_o(alert_tx_o[7]),
    .alert_rx_i(alert_rx_i[7]),

    // Inter-module signals
    .nmi_wdog_timer_bark_o(aon_timer_nmi_wdog_timer_bark_o),
    .wkup_req_o(pwrmgr_wakeups[4]),
    .aon_timer_rst_req_o(pwrmgr_rstreqs[1]),
    .lc_escalate_en_i(lc_ctrl_lc_escalate_en_i),
    .sleep_mode_i(pwrmgr_low_power),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(aon_timer_tl_req_i),
    .tl_o(aon_timer_tl_rsp_o)
  );

  ast_part_secondary #(
    .UsbCalibWidth(AstUsbCalibWidth),
    .Pad2AstInWidth(AstPad2AstInWidth),
    .Ast2PadOutWidth(AstAst2PadOutWidth)
  ) u_ast_part_secondary (
    // Clock and reset connections
    .clk_ast_adc_i(clkmgr_clocks.clk_aon_peri),
    .clk_ast_alert_i(clkmgr_clocks.clk_io_div4_secure),
    .clk_ast_es_i(clkmgr_clocks.clk_main_secure),
    .clk_ast_rng_i(clkmgr_clocks.clk_main_secure),
    .clk_ast_tlul_i(clkmgr_clocks.clk_io_div4_infra),
    .clk_ast_usb_i(clkmgr_clocks.clk_usb_peri),
    .clk_ast_ext_i(clk_ast_ext_i),
    .rst_ast_adc_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_ast_alert_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_es_ni(rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_rng_ni(rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_tlul_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_usb_ni(rstmgr_resets.rst_usb_n[rstmgr_pkg::DomainMainSel]),


    // Inter-module signals
    .usb_io_pu_cal_o(usb_io_pu_cal_o),
    .adc_i(ast_adc_req),
    .adc_o(ast_adc_rsp),
    .adc_a0_a_i(ast_adc_a0_a_i),
    .adc_a1_a_i(ast_adc_a1_a_i),
    .ast2pad_t0_a_o(ast2pad_t0_a_o),
    .ast2pad_t1_a_o(ast2pad_t1_a_o),
    .padmux2ast_i(padmux2ast_i),
    .ast2padmux_o(ast_ast2padmux),
    .por_n_i(manual_in_por_n_i),
    .sns_clks_i(ast_sns_clks),
    .sns_rsts_i(ast_sns_rsts),
    .sns_spi_ext_clk_i(spi_device_sck_monitor_i),
    .vx_supp_i(ast_vx_supp_i),
    .ast_pwst_o(),
    .ast_pwst_h_o(ast_pwst_h_o),
    .rstmgr_por_n_o(rstmgr_por_n),
    .io_pwr_st_o(ast_io_pwr_st),
    .pwrmgr_i(pwrmgr_pwr_ast_req),
    .pwrmgr_o(pwrmgr_pwr_ast_rsp),
    .flash_power_down_h_o(),
    .flash_power_ready_h_o(),
    .otp_power_seq_i('0),
    .otp_power_seq_h_o(),
    .clk_src_aon_o(ast_clk_src_aon),
    .usb_ref_pulse_i(usbdev_usb_ref_pulse_i),
    .usb_ref_val_i(usbdev_usb_ref_val_i),
    .alert_o(sensor_ctrl_ast_alert_req),
    .alert_i(sensor_ctrl_ast_alert_rsp),
    .dft_strap_test_i(pinmux_dft_strap_test_i),
    .lc_dft_en_i(lc_ctrl_lc_dft_en_i),
    .obs_i(ast_obs_i),
    .obs_ctrl_o(ast_obs_ctrl_o),
    .mux_iob_sel_o(mux_iob_sel_o),
    .flash_bist_en_o(),
    .dft_scan_md_o(scanmode_o),
    .scan_shift_en_o(scan_en_o),
    .scan_reset_n_o(scan_rst_n_o),
    .mem_cfg_o(ast_mem_cfg_req),
    .mem_cfg_i(ast_mem_cfg_rsp),
    .clk_osc_byp_i(ast_clk_osc_byp),
    .ext_freq_is_96m_i(clkmgr_hi_speed_sel),
    .all_clk_byp_req_i(clkmgr_all_clk_byp_req),
    .io_clk_byp_req_i(clkmgr_io_clk_byp_req),
    .intraip_s2p_o(ast_intraip_s2p_o),
    .intraip_p2s_i(ast_intraip_p2s_i)
  );

  sensor_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[31:30]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_sensor_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_secure),
    .clk_aon_i(clkmgr_clocks.clk_aon_secure),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_io_status_change_o  (intr_sensor_ctrl_io_status_change),
    .intr_init_status_change_o(intr_sensor_ctrl_init_status_change),

    // alert_handler[30]: recov_alert
    // alert_handler[31]: fatal_alert
    .alert_tx_o(alert_tx_o[9:8]),
    .alert_rx_i(alert_rx_i[9:8]),

    // CIO outputs
    .cio_ast_debug_out_o   (cio_sensor_ctrl_ast_debug_out_d2p_o),
    .cio_ast_debug_out_en_o(cio_sensor_ctrl_ast_debug_out_en_d2p_o),

    // Inter-module signals
    .ast_alert_i(sensor_ctrl_ast_alert_req),
    .ast_alert_o(sensor_ctrl_ast_alert_rsp),
    .ast_status_i(ast_io_pwr_st),
    .ast_init_done_i(ast_init_done_i),
    .ast2pinmux_i(ast_ast2padmux),
    .wkup_req_o(pwrmgr_wakeups[5]),
    .manual_pad_attr_o(sensor_ctrl_manual_pad_attr_o),
    .tl_i(sensor_ctrl_tl_req_i),
    .tl_o(sensor_ctrl_tl_rsp_o)
  );

  sram_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[32]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .RndCnstSramKey(RndCnstSramCtrlRetSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlRetSramNonce),
    .RndCnstLfsrSeed(RndCnstSramCtrlRetLfsrSeed),
    .RndCnstLfsrPerm(RndCnstSramCtrlRetLfsrPerm),
    .MemSizeRam(4096),
    .InstSize(SramCtrlRetInstSize),
    .NumRamInst(SramCtrlRetNumRamInst),
    .InstrExec(SramCtrlRetInstrExec),
    .NumPrinceRoundsHalf(SramCtrlRetNumPrinceRoundsHalf),
    .NumAddrScrRounds(SramCtrlRetNumAddrScrRounds),
    .Outstanding(SramCtrlRetOutstanding),
    .EccCorrection(SramCtrlRetEccCorrection)
  ) u_sram_ctrl_ret (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_infra),
    .clk_otp_i(clkmgr_clocks.clk_io_div4_infra),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_otp_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),

    // alert_handler[32]: fatal_error
    .alert_tx_o(alert_tx_o[10]),
    .alert_rx_i(alert_rx_i[10]),

    // RACL policies
    .racl_policy_sel_ranges_ram_i('{top_racl_pkg::RACL_RANGE_T_DEFAULT}),

    // Inter-module signals
    .sram_otp_key_o(otp_ctrl_sram_otp_key_req_o),
    .sram_otp_key_i(otp_ctrl_sram_otp_key_rsp_i),
    .ram_cfg_i(sram_ctrl_ret_ram_cfg_req),
    .ram_cfg_o(sram_ctrl_ret_ram_cfg_rsp),
    .lc_escalate_en_i(lc_ctrl_lc_escalate_en_i),
    .lc_hw_debug_en_i(lc_ctrl_pkg::Off),
    .otp_en_sram_ifetch_i(prim_mubi_pkg::MuBi8False),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .sram_rerror_o(),
    .regs_tl_i(sram_ctrl_ret_regs_tl_req_i),
    .regs_tl_o(sram_ctrl_ret_regs_tl_rsp_o),
    .ram_tl_i(sram_ctrl_ret_ram_tl_req_i),
    .ram_tl_o(sram_ctrl_ret_ram_tl_rsp_o)
  );


  // Interrupt vector to PLIC rv_plic in power domain Main
  assign intr_vector_o = {
    intr_sensor_ctrl_init_status_change,
    intr_sensor_ctrl_io_status_change,
    intr_aon_timer_wdog_timer_bark,
    intr_aon_timer_wkup_timer_expired,
    intr_adc_ctrl_match_pending,
    intr_sysrst_ctrl_event_detected,
    intr_pwrmgr_wakeup
  };



  // Connect clkmgr to top-level signals for other power domains
  assign clkmgr_clocks_o = clkmgr_clocks;
  assign clkmgr_cg_en_o  = clkmgr_cg_en;

  // Connect rstmgr to top-level signals for other power domains
  assign rstmgr_resets_o = rstmgr_resets;
  assign rstmgr_rst_en_o = rstmgr_rst_en;

  // Connect AST senses to clocks and resets
  assign ast_sns_clks = clkmgr_clocks;
  assign ast_sns_rsts = rstmgr_resets;

  // Tie-off unused clock gate signal
  logic unused_cg_en_ast_ext;
  assign unused_cg_en_ast_ext = ^cg_en_ast_ext_i;

  // Connect local memory configurations
  assign sram_ctrl_ret_ram_cfg_req     = ast_mem_cfg_req.sram_ctrl_ret;
  assign ast_mem_cfg_rsp.sram_ctrl_ret = sram_ctrl_ret_ram_cfg_rsp;

  // Make sure scanmode is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_o, ast_clk_src_sys_i, 0)

endmodule
