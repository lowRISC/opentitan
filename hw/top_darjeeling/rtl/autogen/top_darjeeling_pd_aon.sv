// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
//                -o hw/top_darjeeling/

`include "prim_assert.sv"

module top_darjeeling_pd_aon #(
  // TODO Manual parameters for pwrmgr
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
  // Auto-inferred parameters
  // parameters for pwrmgr_aon
  // parameters for rstmgr_aon
  parameter bit SecRstmgrAonCheck = 1'b1,
  parameter int SecRstmgrAonMaxSyncDelay = 2,
  // parameters for clkmgr_aon
  // parameters for aon_timer_aon
  // parameters for soc_proxy
  // parameters for sram_ctrl_ret_aon
  parameter int SramCtrlRetAonInstSize = 4096,
  parameter int SramCtrlRetAonNumRamInst = 1,
  parameter bit SramCtrlRetAonInstrExec = 0,
  parameter int SramCtrlRetAonNumPrinceRoundsHalf = 3,
  parameter int SramCtrlRetAonNumAddrScrRounds = 2,
  parameter bit SramCtrlRetAonEccCorrection = 0
) (
  // Inter-module Signal External type
  input  alert_handler_pkg::alert_crashdump_t       alert_handler_crashdump_i,
  output prim_esc_pkg::esc_rx_t       alert_handler_esc_rx_o,
  input  prim_esc_pkg::esc_tx_t       alert_handler_esc_tx_i,
  output logic       aon_timer_aon_nmi_wdog_timer_bark_o,
  output otp_ctrl_pkg::sram_otp_key_req_t       otp_ctrl_sram_otp_key_req_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t       otp_ctrl_sram_otp_key_rsp_i,
  output pwrmgr_pkg::pwr_otp_req_t       pwrmgr_aon_pwr_otp_req_o,
  input  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_aon_pwr_otp_rsp_i,
  output lc_ctrl_pkg::pwr_lc_req_t       pwrmgr_aon_pwr_lc_req_o,
  input  lc_ctrl_pkg::pwr_lc_rsp_t       pwrmgr_aon_pwr_lc_rsp_i,
  output logic       pwrmgr_aon_strap_o,
  output logic       pwrmgr_aon_low_power_o,
  output lc_ctrl_pkg::lc_tx_t       pwrmgr_aon_fetch_en_o,
  input  rom_ctrl_pkg::pwrmgr_data_t [2:0] pwrmgr_aon_rom_ctrl_i,
  output pwrmgr_pkg::pwr_boot_status_t       pwrmgr_aon_boot_status_o,
  output dma_pkg::lsio_trigger_t       dma_lsio_trigger_o,
  input  logic       i2c0_lsio_trigger_i,
  input  logic       spi_host0_lsio_trigger_i,
  input  logic       uart0_lsio_trigger_i,
  input  prim_mubi_pkg::mubi4_t [3:0] clkmgr_aon_idle_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en_i,
  input  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump_i,
  input  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr_i,
  input  logic       rv_dm_ndmreset_req_i,
  input  tlul_pkg::tl_h2d_t       soc_proxy_dma_tl_h2d_i,
  output tlul_pkg::tl_d2h_t       soc_proxy_dma_tl_d2h_o,
  output tlul_pkg::tl_h2d_t       soc_proxy_ctn_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t       soc_proxy_ctn_tl_d2h_i,
  input  logic       pwrmgr_aon_wakeups_i,
  input  tlul_pkg::tl_h2d_t       soc_proxy_core_tl_req_i,
  output tlul_pkg::tl_d2h_t       soc_proxy_core_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       soc_proxy_ctn_tl_req_i,
  output tlul_pkg::tl_d2h_t       soc_proxy_ctn_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       pwrmgr_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       pwrmgr_aon_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       rstmgr_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       rstmgr_aon_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       clkmgr_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       clkmgr_aon_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_regs_tl_req_i,
  output tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_regs_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_ram_tl_req_i,
  output tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_ram_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       aon_timer_aon_tl_req_i,
  output tlul_pkg::tl_d2h_t       aon_timer_aon_tl_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_t [SramCtrlRetAonNumRamInst-1:0] sram_ctrl_ret_aon_ram_1p_cfg_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlRetAonNumRamInst-1:0] sram_ctrl_ret_aon_ram_1p_cfg_rsp_o,
  output pwrmgr_pkg::pwr_boot_status_t       pwrmgr_boot_status_o,
  input  logic       pwrmgr_ext_rst_ack_i,
  output clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks_o,
  output clkmgr_pkg::clkmgr_cg_en_t       clkmgr_aon_cg_en_o,
  output prim_mubi_pkg::mubi4_t       clk_main_jitter_en_o,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_ast_rsp_i,
  input  logic [1:0] por_n_i,
  output rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets_o,
  output rstmgr_pkg::rstmgr_rst_en_t       rstmgr_aon_rst_en_o,
  input  tlul_pkg::tl_h2d_t       ctn_misc_tl_h2d_i,
  output tlul_pkg::tl_d2h_t       ctn_misc_tl_d2h_o,
  input  logic       soc_wkup_async_i,
  input  logic       soc_rst_req_async_i,
  input  logic [7:0] soc_lsio_trigger_i,
  output logic [15:0] soc_gpi_async_o,
  input  logic [15:0] soc_gpo_async_i,
  input  logic [3:0] integrator_id_i,
  input  logic [15:0] cio_soc_proxy_soc_gpi_p2d_i,
  output logic [15:0] cio_soc_proxy_soc_gpo_d2p_o,
  output logic [15:0] cio_soc_proxy_soc_gpo_en_d2p_o,

  // Interrupts to PLIC rv_plic in power domain Main
  output logic [2:0] intr_vector_o,

  // Alerts to power domain Main
  input  prim_alert_pkg::alert_rx_t [7:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [7:0] alert_tx_o,

  // Externally supplied clocks
  input clk_main_i,
  input clk_io_i,
  input clk_aon_i,


  // Manual DFT signals
  input                        scan_rst_ni, // reset used for test mode
  input prim_mubi_pkg::mubi4_t scanmode_i   // lc_ctrl_pkg::On for Scan
);

  import top_darjeeling_pkg::*;
  // Compile-time random constants
  import top_darjeeling_rnd_cnst_pkg::*;

  // Local Parameters
  // local parameters for sram_ctrl_ret_aon
  localparam int SramCtrlRetAonOutstanding = 2;

  // Signals


  // Interrupt source list
  logic intr_pwrmgr_aon_wakeup;
  logic intr_aon_timer_aon_wkup_timer_expired;
  logic intr_aon_timer_aon_wdog_timer_bark;

  // Alert list


  // Define inter-module signals
  pwrmgr_pkg::pwr_rst_req_t       pwrmgr_aon_pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t       pwrmgr_aon_pwr_rst_rsp;
  pwrmgr_pkg::pwr_clk_req_t       pwrmgr_aon_pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t       pwrmgr_aon_pwr_clk_rsp;
  logic       pwrmgr_aon_low_power;
  pwrmgr_pkg::pwr_boot_status_t       pwrmgr_aon_boot_status;
  prim_mubi_pkg::mubi4_t       rstmgr_aon_sw_rst_req;
  logic [2:0] pwrmgr_aon_wakeups;
  logic [1:0] pwrmgr_aon_rstreqs;
  clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks;
  clkmgr_pkg::clkmgr_cg_en_t       clkmgr_aon_cg_en;
  rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets;
  rstmgr_pkg::rstmgr_rst_en_t       rstmgr_aon_rst_en;

  // Create mixed connections to ports
  assign pwrmgr_aon_low_power_o = pwrmgr_aon_low_power;
  assign pwrmgr_aon_boot_status_o = pwrmgr_aon_boot_status;
  assign pwrmgr_aon_wakeups[0] = pwrmgr_aon_wakeups_i;
  assign pwrmgr_boot_status_o = pwrmgr_aon_boot_status;
  assign clkmgr_aon_clocks_o = clkmgr_aon_clocks;
  assign clkmgr_aon_cg_en_o = clkmgr_aon_cg_en;
  assign rstmgr_aon_resets_o = rstmgr_aon_resets;
  assign rstmgr_aon_rst_en_o = rstmgr_aon_rst_en;




  // Instantiation of IPs
  pwrmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[14]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .EscNumSeverities(AlertHandlerEscNumSeverities),
    .EscPingCountWidth(AlertHandlerEscPingCountWidth)
  ) u_pwrmgr_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_powerup),
    .clk_slow_i(clkmgr_aon_clocks.clk_aon_powerup),
    .clk_lc_i(clkmgr_aon_clocks.clk_io_powerup),
    .clk_esc_i(clkmgr_aon_clocks.clk_io_secure),
    .rst_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_main_ni(rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::DomainMainSel]),
    .rst_lc_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_esc_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_slow_ni(rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_wakeup_o(intr_pwrmgr_aon_wakeup),

    // alert_handler[14]: fatal_fault
    .alert_tx_o(alert_tx_o[0]),
    .alert_rx_i(alert_rx_i[0]),

    // Inter-module signals
    .boot_status_o(pwrmgr_aon_boot_status),
    .ext_rst_ack_i(pwrmgr_ext_rst_ack_i),
    .pwr_ast_o(pwrmgr_ast_req_o),
    .pwr_ast_i(pwrmgr_ast_rsp_i),
    .pwr_rst_o(pwrmgr_aon_pwr_rst_req),
    .pwr_rst_i(pwrmgr_aon_pwr_rst_rsp),
    .pwr_clk_o(pwrmgr_aon_pwr_clk_req),
    .pwr_clk_i(pwrmgr_aon_pwr_clk_rsp),
    .pwr_otp_o(pwrmgr_aon_pwr_otp_req_o),
    .pwr_otp_i(pwrmgr_aon_pwr_otp_rsp_i),
    .pwr_lc_o(pwrmgr_aon_pwr_lc_req_o),
    .pwr_lc_i(pwrmgr_aon_pwr_lc_rsp_i),
    .pwr_nvm_i(pwrmgr_pkg::PWR_NVM_DEFAULT),
    .esc_rst_tx_i(alert_handler_esc_tx_i),
    .esc_rst_rx_o(alert_handler_esc_rx_o),
    .pwr_cpu_i(rv_core_ibex_pwrmgr_i),
    .wakeups_i(pwrmgr_aon_wakeups),
    .rstreqs_i(pwrmgr_aon_rstreqs),
    .ndmreset_req_i(rv_dm_ndmreset_req_i),
    .strap_o(pwrmgr_aon_strap_o),
    .low_power_o(pwrmgr_aon_low_power),
    .rom_ctrl_i(pwrmgr_aon_rom_ctrl_i),
    .fetch_en_o(pwrmgr_aon_fetch_en_o),
    .lc_dft_en_i(lc_ctrl_lc_dft_en_i),
    .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en_i),
    .sw_rst_req_i(rstmgr_aon_sw_rst_req),
    .tl_i(pwrmgr_aon_tl_req_i),
    .tl_o(pwrmgr_aon_tl_rsp_o)
  );

  rstmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[16:15]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .SecCheck(SecRstmgrAonCheck),
    .SecMaxSyncDelay(SecRstmgrAonMaxSyncDelay)
  ) u_rstmgr_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_powerup),
    .clk_por_i(clkmgr_aon_clocks.clk_io_powerup),
    .clk_aon_i(clkmgr_aon_clocks.clk_aon_powerup),
    .clk_main_i(clkmgr_aon_clocks.clk_main_powerup),
    .clk_io_i(clkmgr_aon_clocks.clk_io_powerup),
    .rst_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_por_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i,
    .scan_rst_ni,

    // alert_handler[15]: fatal_fault
    // alert_handler[16]: fatal_cnsty_fault
    .alert_tx_o(alert_tx_o[2:1]),
    .alert_rx_i(alert_rx_i[2:1]),

    // Inter-module signals
    .por_n_i(por_n_i),
    .pwr_i(pwrmgr_aon_pwr_rst_req),
    .pwr_o(pwrmgr_aon_pwr_rst_rsp),
    .resets_o(rstmgr_aon_resets),
    .rst_en_o(rstmgr_aon_rst_en),
    .alert_dump_i(alert_handler_crashdump_i),
    .cpu_dump_i(rv_core_ibex_crash_dump_i),
    .sw_rst_req_o(rstmgr_aon_sw_rst_req),
    .tl_i(rstmgr_aon_tl_req_i),
    .tl_o(rstmgr_aon_tl_rsp_o)
  );

  clkmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[18:17]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_clkmgr_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_powerup),
    .clk_main_i(clk_main_i),
    .clk_io_i(clk_io_i),
    .clk_aon_i(clk_aon_i),
    .rst_shadowed_ni(rstmgr_aon_resets.rst_lc_io_shadowed_n[rstmgr_pkg::DomainAonSel]),
    .rst_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_io_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_main_ni(rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_io_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_root_main_ni(rstmgr_aon_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i,

    // alert_handler[17]: recov_fault
    // alert_handler[18]: fatal_fault
    .alert_tx_o(alert_tx_o[4:3]),
    .alert_rx_i(alert_rx_i[4:3]),

    // Inter-module signals
    .clocks_o(clkmgr_aon_clocks),
    .cg_en_o(clkmgr_aon_cg_en),
    .jitter_en_o(clk_main_jitter_en_o),
    .pwr_i(pwrmgr_aon_pwr_clk_req),
    .pwr_o(pwrmgr_aon_pwr_clk_rsp),
    .idle_i(clkmgr_aon_idle_i),
    .tl_i(clkmgr_aon_tl_req_i),
    .tl_o(clkmgr_aon_tl_rsp_o)
  );

  aon_timer #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[20]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_aon_timer_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_timers),
    .clk_aon_i(clkmgr_aon_clocks.clk_aon_timers),
    .rst_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_wkup_timer_expired_o(intr_aon_timer_aon_wkup_timer_expired),
    .intr_wdog_timer_bark_o   (intr_aon_timer_aon_wdog_timer_bark),

    // alert_handler[20]: fatal_fault
    .alert_tx_o(alert_tx_o[5]),
    .alert_rx_i(alert_rx_i[5]),

    // Inter-module signals
    .nmi_wdog_timer_bark_o(aon_timer_aon_nmi_wdog_timer_bark_o),
    .wkup_req_o(pwrmgr_aon_wakeups[1]),
    .aon_timer_rst_req_o(pwrmgr_aon_rstreqs[0]),
    .lc_escalate_en_i(lc_ctrl_lc_escalate_en_i),
    .sleep_mode_i(pwrmgr_aon_low_power),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(aon_timer_aon_tl_req_i),
    .tl_o(aon_timer_aon_tl_rsp_o)
  );

  soc_proxy #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[21]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_soc_proxy (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_main_infra),
    .clk_aon_i(clkmgr_aon_clocks.clk_aon_infra),
    .rst_ni(rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .rst_por_ni(rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),

    // alert_handler[21]: fatal_alert_intg
    .alert_tx_o(alert_tx_o[6]),
    .alert_rx_i(alert_rx_i[6]),

    // CIO inputs
    .cio_soc_gpi_i   (cio_soc_proxy_soc_gpi_p2d_i),

    // CIO outputs
    .cio_soc_gpo_o   (cio_soc_proxy_soc_gpo_d2p_o),
    .cio_soc_gpo_en_o(cio_soc_proxy_soc_gpo_en_d2p_o),

    // Inter-module signals
    .dma_tl_h2d_i(soc_proxy_dma_tl_h2d_i),
    .dma_tl_d2h_o(soc_proxy_dma_tl_d2h_o),
    .misc_tl_h2d_i(ctn_misc_tl_h2d_i),
    .misc_tl_d2h_o(ctn_misc_tl_d2h_o),
    .wkup_external_req_o(pwrmgr_aon_wakeups[2]),
    .rst_req_external_o(pwrmgr_aon_rstreqs[1]),
    .ctn_tl_h2d_o(soc_proxy_ctn_tl_h2d_o),
    .ctn_tl_d2h_i(soc_proxy_ctn_tl_d2h_i),
    .i2c_lsio_trigger_i(i2c0_lsio_trigger_i),
    .spi_host_lsio_trigger_i(spi_host0_lsio_trigger_i),
    .uart_lsio_trigger_i(uart0_lsio_trigger_i),
    .soc_lsio_trigger_i(soc_lsio_trigger_i),
    .dma_lsio_trigger_o(dma_lsio_trigger_o),
    .soc_wkup_async_i(soc_wkup_async_i),
    .soc_rst_req_async_i(soc_rst_req_async_i),
    .soc_gpi_async_o(soc_gpi_async_o),
    .soc_gpo_async_i(soc_gpo_async_i),
    .integrator_id_i(integrator_id_i),
    .core_tl_i(soc_proxy_core_tl_req_i),
    .core_tl_o(soc_proxy_core_tl_rsp_o),
    .ctn_tl_i(soc_proxy_ctn_tl_req_i),
    .ctn_tl_o(soc_proxy_ctn_tl_rsp_o)
  );

  sram_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[22]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .RndCnstSramKey(RndCnstSramCtrlRetAonSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlRetAonSramNonce),
    .RndCnstLfsrSeed(RndCnstSramCtrlRetAonLfsrSeed),
    .RndCnstLfsrPerm(RndCnstSramCtrlRetAonLfsrPerm),
    .MemSizeRam(4096),
    .InstSize(SramCtrlRetAonInstSize),
    .NumRamInst(SramCtrlRetAonNumRamInst),
    .InstrExec(SramCtrlRetAonInstrExec),
    .NumPrinceRoundsHalf(SramCtrlRetAonNumPrinceRoundsHalf),
    .NumAddrScrRounds(SramCtrlRetAonNumAddrScrRounds),
    .Outstanding(SramCtrlRetAonOutstanding),
    .EccCorrection(SramCtrlRetAonEccCorrection)
  ) u_sram_ctrl_ret_aon (
    // Clock and reset connections
    .clk_i(clkmgr_aon_clocks.clk_io_infra),
    .clk_otp_i(clkmgr_aon_clocks.clk_io_infra),
    .rst_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),
    .rst_otp_ni(rstmgr_aon_resets.rst_lc_io_n[rstmgr_pkg::DomainAonSel]),

    // alert_handler[22]: fatal_error
    .alert_tx_o(alert_tx_o[7]),
    .alert_rx_i(alert_rx_i[7]),

    // RACL policies
    .racl_policy_sel_ranges_ram_i('{top_racl_pkg::RACL_RANGE_T_DEFAULT}),

    // Inter-module signals
    .sram_otp_key_o(otp_ctrl_sram_otp_key_req_o),
    .sram_otp_key_i(otp_ctrl_sram_otp_key_rsp_i),
    .cfg_i(sram_ctrl_ret_aon_ram_1p_cfg_i),
    .cfg_rsp_o(sram_ctrl_ret_aon_ram_1p_cfg_rsp_o),
    .lc_escalate_en_i(lc_ctrl_lc_escalate_en_i),
    .lc_hw_debug_en_i(lc_ctrl_pkg::Off),
    .otp_en_sram_ifetch_i(prim_mubi_pkg::MuBi8False),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .sram_rerror_o(),
    .regs_tl_i(sram_ctrl_ret_aon_regs_tl_req_i),
    .regs_tl_o(sram_ctrl_ret_aon_regs_tl_rsp_o),
    .ram_tl_i(sram_ctrl_ret_aon_ram_tl_req_i),
    .ram_tl_o(sram_ctrl_ret_aon_ram_tl_rsp_o)
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
