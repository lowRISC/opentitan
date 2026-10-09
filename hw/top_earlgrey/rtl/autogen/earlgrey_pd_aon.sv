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
  // parameters for pinmux
  parameter bit SecPinmuxVolatileRawUnlockEn = top_pkg::SecVolatileRawUnlockEn,
  parameter pinmux_pkg::target_cfg_t PinmuxTargetCfg = pinmux_pkg::DefaultTargetCfg,
  // parameters for ast
  parameter int unsigned AstUsbCalibWidth = 20,
  parameter int unsigned AstPad2AstInWidth = 8,
  // parameters for sram_ctrl_ret
  parameter int SramCtrlRetInstSize = 4096,
  parameter int SramCtrlRetNumRamInst = 1,
  parameter bit SramCtrlRetInstrExec = 0,
  parameter int SramCtrlRetNumPrinceRoundsHalf = 3,
  parameter int SramCtrlRetNumAddrScrRounds = 2,
  parameter bit SramCtrlRetEccCorrection = 0,
  parameter bit SecSramCtrlRetZeroInit = 0
) (
  // Inter-module Signal External type
  output ast_pkg::ast_obs_ctrl_t       ast_obs_ctrl_o,
  output prim_mubi_pkg::mubi4_t       ast_clk_src_sys_jen_o,
  input  prim_mubi_pkg::mubi4_t       ast_init_done_i,
  input  logic       spi_device_sck_monitor_i,
  input  logic       usbdev_usb_ref_pulse_i,
  input  logic       usbdev_usb_ref_val_i,
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
  output lc_ctrl_pkg::lc_tx_t       pwrmgr_fetch_en_o,
  input  rom_ctrl_pkg::pwrmgr_data_t       rom_ctrl_pwrmgr_data_i,
  input  logic       usbdev_usb_dp_pullup_i,
  input  logic       usbdev_usb_dn_pullup_i,
  input  logic       usbdev_usb_aon_suspend_req_i,
  input  logic       usbdev_usb_aon_wake_ack_i,
  output logic       usbdev_usb_aon_bus_not_idle_o,
  output logic       usbdev_usb_aon_bus_reset_o,
  output logic       usbdev_usb_aon_sense_lost_o,
  output logic       pinmux_usbdev_wake_detect_active_o,
  input  prim_mubi_pkg::mubi4_t [3:0] clkmgr_idle_i,
  output jtag_pkg::jtag_req_t       pinmux_lc_jtag_req_o,
  input  jtag_pkg::jtag_rsp_t       pinmux_lc_jtag_rsp_i,
  output jtag_pkg::jtag_req_t       pinmux_rv_jtag_req_o,
  input  jtag_pkg::jtag_rsp_t       pinmux_rv_jtag_rsp_i,
  output lc_ctrl_pkg::lc_tx_t       pinmux_pinmux_hw_debug_en_o,
  input  logic       lc_ctrl_strap_en_override_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_clr_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_check_byp_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_req_i,
  output lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_ack_o,
  input  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump_i,
  input  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr_i,
  input  logic       rv_dm_ndmreset_req_i,
  output ast_intraip_pkg::s2p_t       ast_intraip_s2p_o,
  input  ast_intraip_pkg::p2s_t       ast_intraip_p2s_i,
  input  tlul_pkg::tl_h2d_t       pwrmgr_tl_req_i,
  output tlul_pkg::tl_d2h_t       pwrmgr_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       rstmgr_tl_req_i,
  output tlul_pkg::tl_d2h_t       rstmgr_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       clkmgr_tl_req_i,
  output tlul_pkg::tl_d2h_t       clkmgr_tl_rsp_o,
  input  tlul_pkg::tl_h2d_t       pinmux_tl_req_i,
  output tlul_pkg::tl_d2h_t       pinmux_tl_rsp_o,
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
  input  logic       dft_hold_tap_sel_i,
  output logic       usb_dp_pullup_en_o,
  output logic       usb_dn_pullup_en_o,
  output prim_pad_wrapper_pkg::pad_attr_t [3:0] sensor_ctrl_manual_pad_attr_o,
  output logic       cio_uart0_rx_p2d_o,
  input  logic       cio_uart0_tx_d2p_i,
  input  logic       cio_uart0_tx_en_d2p_i,
  output logic       cio_uart1_rx_p2d_o,
  input  logic       cio_uart1_tx_d2p_i,
  input  logic       cio_uart1_tx_en_d2p_i,
  output logic       cio_uart2_rx_p2d_o,
  input  logic       cio_uart2_tx_d2p_i,
  input  logic       cio_uart2_tx_en_d2p_i,
  output logic       cio_uart3_rx_p2d_o,
  input  logic       cio_uart3_tx_d2p_i,
  input  logic       cio_uart3_tx_en_d2p_i,
  input  logic [31:0] cio_gpio_gpio_d2p_i,
  input  logic [31:0] cio_gpio_gpio_en_d2p_i,
  output logic [31:0] cio_gpio_gpio_p2d_o,
  input  logic [3:0] cio_spi_device_sd_d2p_i,
  input  logic [3:0] cio_spi_device_sd_en_d2p_i,
  output logic [3:0] cio_spi_device_sd_p2d_o,
  output logic       cio_spi_device_sck_p2d_o,
  output logic       cio_spi_device_csb_p2d_o,
  output logic       cio_spi_device_tpm_csb_p2d_o,
  input  logic       cio_i2c0_sda_d2p_i,
  input  logic       cio_i2c0_sda_en_d2p_i,
  output logic       cio_i2c0_sda_p2d_o,
  input  logic       cio_i2c0_scl_d2p_i,
  input  logic       cio_i2c0_scl_en_d2p_i,
  output logic       cio_i2c0_scl_p2d_o,
  input  logic       cio_i2c1_sda_d2p_i,
  input  logic       cio_i2c1_sda_en_d2p_i,
  output logic       cio_i2c1_sda_p2d_o,
  input  logic       cio_i2c1_scl_d2p_i,
  input  logic       cio_i2c1_scl_en_d2p_i,
  output logic       cio_i2c1_scl_p2d_o,
  input  logic       cio_i2c2_sda_d2p_i,
  input  logic       cio_i2c2_sda_en_d2p_i,
  output logic       cio_i2c2_sda_p2d_o,
  input  logic       cio_i2c2_scl_d2p_i,
  input  logic       cio_i2c2_scl_en_d2p_i,
  output logic       cio_i2c2_scl_p2d_o,
  input  logic       cio_i3c0_scl_d2p_i,
  input  logic       cio_i3c0_scl_en_d2p_i,
  output logic       cio_i3c0_scl_p2d_o,
  input  logic       cio_i3c0_sda_d2p_i,
  input  logic       cio_i3c0_sda_en_d2p_i,
  output logic       cio_i3c0_sda_p2d_o,
  input  logic       cio_i3c0_ctrl_scl_pu_d2p_i,
  input  logic       cio_i3c0_ctrl_scl_pu_en_d2p_i,
  input  logic       cio_i3c0_ctrl_sda_pu_d2p_i,
  input  logic       cio_i3c0_ctrl_sda_pu_en_d2p_i,
  input  logic       cio_i3c0_scl_hk_d2p_i,
  input  logic       cio_i3c0_scl_hk_en_d2p_i,
  input  logic       cio_i3c0_sda_hk_d2p_i,
  input  logic       cio_i3c0_sda_hk_en_d2p_i,
  input  logic       cio_i3c1_scl_d2p_i,
  input  logic       cio_i3c1_scl_en_d2p_i,
  output logic       cio_i3c1_scl_p2d_o,
  input  logic       cio_i3c1_sda_d2p_i,
  input  logic       cio_i3c1_sda_en_d2p_i,
  output logic       cio_i3c1_sda_p2d_o,
  input  logic       cio_i3c1_ctrl_scl_pu_d2p_i,
  input  logic       cio_i3c1_ctrl_scl_pu_en_d2p_i,
  input  logic       cio_i3c1_ctrl_sda_pu_d2p_i,
  input  logic       cio_i3c1_ctrl_sda_pu_en_d2p_i,
  input  logic       cio_i3c1_scl_hk_d2p_i,
  input  logic       cio_i3c1_scl_hk_en_d2p_i,
  input  logic       cio_i3c1_sda_hk_d2p_i,
  input  logic       cio_i3c1_sda_hk_en_d2p_i,
  input  logic [3:0] cio_spi_host0_sd_d2p_i,
  input  logic [3:0] cio_spi_host0_sd_en_d2p_i,
  output logic [3:0] cio_spi_host0_sd_p2d_o,
  input  logic       cio_spi_host0_sck_d2p_i,
  input  logic       cio_spi_host0_sck_en_d2p_i,
  input  logic       cio_spi_host0_csb_d2p_i,
  input  logic       cio_spi_host0_csb_en_d2p_i,
  input  logic [3:0] cio_spi_host1_sd_d2p_i,
  input  logic [3:0] cio_spi_host1_sd_en_d2p_i,
  output logic [3:0] cio_spi_host1_sd_p2d_o,
  input  logic       cio_spi_host1_sck_d2p_i,
  input  logic       cio_spi_host1_sck_en_d2p_i,
  input  logic       cio_spi_host1_csb_d2p_i,
  input  logic       cio_spi_host1_csb_en_d2p_i,
  input  logic       cio_usbdev_usb_dp_d2p_i,
  input  logic       cio_usbdev_usb_dp_en_d2p_i,
  output logic       cio_usbdev_usb_dp_p2d_o,
  input  logic       cio_usbdev_usb_dn_d2p_i,
  input  logic       cio_usbdev_usb_dn_en_d2p_i,
  output logic       cio_usbdev_usb_dn_p2d_o,
  output logic       cio_usbdev_sense_p2d_o,
  output logic       cio_rram_macro_tck_p2d_o,
  output logic       cio_rram_macro_tms_p2d_o,
  output logic       cio_rram_macro_tdi_p2d_o,
  input  logic       cio_rram_macro_tdo_d2p_i,
  input  logic       cio_rram_macro_tdo_en_d2p_i,
  input  logic       ast_clk_src_sys_i,
  input  logic       ast_clk_src_io_i,
  input  logic       ast_clk_src_usb_i,

  // Multiplexed I/O
  input  logic [46:0] mio_in_i,
  output logic [46:0] mio_out_o,
  output logic [46:0] mio_oe_o,

  // Dedicated I/O
  input  logic [15:0] dio_in_i,
  output logic [15:0] dio_out_o,
  output logic [15:0] dio_oe_o,

  // Pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,

  // Interrupts to PLIC rv_plic in power domain Main
  output logic [6:0] intr_vector_o,

  // Alerts to power domain Main
  input  prim_alert_pkg::alert_rx_t [11:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [11:0] alert_tx_o,

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
  logic [60:0] mio_p2d;
  logic [75:0] mio_d2p;
  logic [75:0] mio_en_d2p;
  logic [15:0] dio_p2d;
  logic [15:0] dio_d2p;
  logic [15:0] dio_en_d2p;
  // pwrmgr
  // rstmgr
  // clkmgr
  // sysrst_ctrl
  logic        cio_sysrst_ctrl_ac_present_p2d;
  logic        cio_sysrst_ctrl_key0_in_p2d;
  logic        cio_sysrst_ctrl_key1_in_p2d;
  logic        cio_sysrst_ctrl_key2_in_p2d;
  logic        cio_sysrst_ctrl_pwrb_in_p2d;
  logic        cio_sysrst_ctrl_lid_open_p2d;
  logic        cio_sysrst_ctrl_ec_rst_l_p2d;
  logic        cio_sysrst_ctrl_flash_wp_l_p2d;
  logic        cio_sysrst_ctrl_bat_disable_d2p;
  logic        cio_sysrst_ctrl_bat_disable_en_d2p;
  logic        cio_sysrst_ctrl_key0_out_d2p;
  logic        cio_sysrst_ctrl_key0_out_en_d2p;
  logic        cio_sysrst_ctrl_key1_out_d2p;
  logic        cio_sysrst_ctrl_key1_out_en_d2p;
  logic        cio_sysrst_ctrl_key2_out_d2p;
  logic        cio_sysrst_ctrl_key2_out_en_d2p;
  logic        cio_sysrst_ctrl_pwrb_out_d2p;
  logic        cio_sysrst_ctrl_pwrb_out_en_d2p;
  logic        cio_sysrst_ctrl_z3_wakeup_d2p;
  logic        cio_sysrst_ctrl_z3_wakeup_en_d2p;
  logic        cio_sysrst_ctrl_ec_rst_l_d2p;
  logic        cio_sysrst_ctrl_ec_rst_l_en_d2p;
  logic        cio_sysrst_ctrl_flash_wp_l_d2p;
  logic        cio_sysrst_ctrl_flash_wp_l_en_d2p;
  // adc_ctrl
  // pinmux
  // aon_timer
  // ast
  // sensor_ctrl
  logic [8:0]  cio_sensor_ctrl_ast_debug_out_d2p;
  logic [8:0]  cio_sensor_ctrl_ast_debug_out_en_d2p;
  // sram_ctrl_ret


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
  pinmux_pkg::dft_strap_test_req_t       pinmux_dft_strap_test;
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
  logic       pwrmgr_strap;
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
  jtag_pkg::jtag_req_t       pinmux_dft_jtag_req;
  jtag_pkg::jtag_rsp_t       pinmux_dft_jtag_rsp;

  // Create mixed connections to ports
  assign clkmgr_all_clk_byp_req_o = clkmgr_all_clk_byp_req;
  assign clkmgr_io_clk_byp_req_o = clkmgr_io_clk_byp_req;
  assign clkmgr_hi_speed_sel_o = clkmgr_hi_speed_sel;
  assign ast_clk_osc_byp = clk_osc_byp_pd_aon_i;




  // Instantiation of IPs
  pwrmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[23]),
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

    // alert_handler[23]: fatal_fault
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
    .strap_o(pwrmgr_strap),
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
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[25:24]),
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

    // alert_handler[24]: fatal_fault
    // alert_handler[25]: fatal_cnsty_fault
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
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[27:26]),
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

    // alert_handler[26]: recov_fault
    // alert_handler[27]: fatal_fault
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
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[28]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_sysrst_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_secure),
    .clk_aon_i(clkmgr_clocks.clk_aon_secure),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_event_detected_o(intr_sysrst_ctrl_event_detected),

    // alert_handler[28]: fatal_fault
    .alert_tx_o(alert_tx_o[5]),
    .alert_rx_i(alert_rx_i[5]),

    // CIO inputs
    .cio_ac_present_i    (cio_sysrst_ctrl_ac_present_p2d),
    .cio_key0_in_i       (cio_sysrst_ctrl_key0_in_p2d),
    .cio_key1_in_i       (cio_sysrst_ctrl_key1_in_p2d),
    .cio_key2_in_i       (cio_sysrst_ctrl_key2_in_p2d),
    .cio_pwrb_in_i       (cio_sysrst_ctrl_pwrb_in_p2d),
    .cio_lid_open_i      (cio_sysrst_ctrl_lid_open_p2d),
    .cio_ec_rst_l_i      (cio_sysrst_ctrl_ec_rst_l_p2d),
    .cio_flash_wp_l_i    (cio_sysrst_ctrl_flash_wp_l_p2d),

    // CIO outputs
    .cio_bat_disable_o   (cio_sysrst_ctrl_bat_disable_d2p),
    .cio_bat_disable_en_o(cio_sysrst_ctrl_bat_disable_en_d2p),
    .cio_key0_out_o      (cio_sysrst_ctrl_key0_out_d2p),
    .cio_key0_out_en_o   (cio_sysrst_ctrl_key0_out_en_d2p),
    .cio_key1_out_o      (cio_sysrst_ctrl_key1_out_d2p),
    .cio_key1_out_en_o   (cio_sysrst_ctrl_key1_out_en_d2p),
    .cio_key2_out_o      (cio_sysrst_ctrl_key2_out_d2p),
    .cio_key2_out_en_o   (cio_sysrst_ctrl_key2_out_en_d2p),
    .cio_pwrb_out_o      (cio_sysrst_ctrl_pwrb_out_d2p),
    .cio_pwrb_out_en_o   (cio_sysrst_ctrl_pwrb_out_en_d2p),
    .cio_z3_wakeup_o     (cio_sysrst_ctrl_z3_wakeup_d2p),
    .cio_z3_wakeup_en_o  (cio_sysrst_ctrl_z3_wakeup_en_d2p),
    .cio_ec_rst_l_o      (cio_sysrst_ctrl_ec_rst_l_d2p),
    .cio_ec_rst_l_en_o   (cio_sysrst_ctrl_ec_rst_l_en_d2p),
    .cio_flash_wp_l_o    (cio_sysrst_ctrl_flash_wp_l_d2p),
    .cio_flash_wp_l_en_o (cio_sysrst_ctrl_flash_wp_l_en_d2p),

    // Inter-module signals
    .wkup_req_o(pwrmgr_wakeups[0]),
    .rst_req_o(pwrmgr_rstreqs[0]),
    .tl_i(sysrst_ctrl_tl_req_i),
    .tl_o(sysrst_ctrl_tl_rsp_o)
  );

  adc_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[29]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_adc_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_peri),
    .clk_aon_i(clkmgr_clocks.clk_aon_peri),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),

    // Interrupts
    .intr_match_pending_o(intr_adc_ctrl_match_pending),

    // alert_handler[29]: fatal_fault
    .alert_tx_o(alert_tx_o[6]),
    .alert_rx_i(alert_rx_i[6]),

    // Inter-module signals
    .adc_o(ast_adc_req),
    .adc_i(ast_adc_rsp),
    .wkup_req_o(pwrmgr_wakeups[1]),
    .tl_i(adc_ctrl_tl_req_i),
    .tl_o(adc_ctrl_tl_rsp_o)
  );

  pinmux #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[30]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .SecVolatileRawUnlockEn(SecPinmuxVolatileRawUnlockEn),
    .TargetCfg(PinmuxTargetCfg)
  ) u_pinmux (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_powerup),
    .clk_aon_i(clkmgr_clocks.clk_aon_powerup),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_sys_ni(rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i(scanmode_o),

    // alert_handler[30]: fatal_fault
    .alert_tx_o(alert_tx_o[7]),
    .alert_rx_i(alert_rx_i[7]),

    // Inter-module signals
    .lc_hw_debug_clr_i(lc_ctrl_lc_hw_debug_clr_i),
    .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en_i),
    .lc_dft_en_i(lc_ctrl_lc_dft_en_i),
    .lc_escalate_en_i(lc_ctrl_lc_escalate_en_i),
    .lc_check_byp_en_i(lc_ctrl_lc_check_byp_en_i),
    .pinmux_hw_debug_en_o(pinmux_pinmux_hw_debug_en_o),
    .lc_jtag_o(pinmux_lc_jtag_req_o),
    .lc_jtag_i(pinmux_lc_jtag_rsp_i),
    .rv_jtag_o(pinmux_rv_jtag_req_o),
    .rv_jtag_i(pinmux_rv_jtag_rsp_i),
    .dft_jtag_o(pinmux_dft_jtag_req),
    .dft_jtag_i(pinmux_dft_jtag_rsp),
    .dft_strap_test_o(pinmux_dft_strap_test),
    .dft_hold_tap_sel_i(dft_hold_tap_sel_i),
    .sleep_en_i(pwrmgr_low_power),
    .strap_en_i(pwrmgr_strap),
    .strap_en_override_i(lc_ctrl_strap_en_override_i),
    .pin_wkup_req_o(pwrmgr_wakeups[2]),
    .usbdev_dppullup_en_i(usbdev_usb_dp_pullup_i),
    .usbdev_dnpullup_en_i(usbdev_usb_dn_pullup_i),
    .usb_dppullup_en_o(usb_dp_pullup_en_o),
    .usb_dnpullup_en_o(usb_dn_pullup_en_o),
    .usb_wkup_req_o(pwrmgr_wakeups[3]),
    .usbdev_suspend_req_i(usbdev_usb_aon_suspend_req_i),
    .usbdev_wake_ack_i(usbdev_usb_aon_wake_ack_i),
    .usbdev_bus_not_idle_o(usbdev_usb_aon_bus_not_idle_o),
    .usbdev_bus_reset_o(usbdev_usb_aon_bus_reset_o),
    .usbdev_sense_lost_o(usbdev_usb_aon_sense_lost_o),
    .usbdev_wake_detect_active_o(pinmux_usbdev_wake_detect_active_o),
    .tl_i(pinmux_tl_req_i),
    .tl_o(pinmux_tl_rsp_o),

    .periph_to_mio_i   (mio_d2p   ),
    .periph_to_mio_oe_i(mio_en_d2p),
    .mio_to_periph_o   (mio_p2d   ),

    .mio_attr_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i,

    .periph_to_dio_i   (dio_d2p   ),
    .periph_to_dio_oe_i(dio_en_d2p),
    .dio_to_periph_o   (dio_p2d   ),

    .dio_attr_o,
    .dio_out_o,
    .dio_oe_o,
    .dio_in_i
  );

  aon_timer #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[31]),
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

    // alert_handler[31]: fatal_fault
    .alert_tx_o(alert_tx_o[8]),
    .alert_rx_i(alert_rx_i[8]),

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
    .dft_strap_test_i(pinmux_dft_strap_test),
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
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[33:32]),
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

    // alert_handler[32]: recov_alert
    // alert_handler[33]: fatal_alert
    .alert_tx_o(alert_tx_o[10:9]),
    .alert_rx_i(alert_rx_i[10:9]),

    // CIO outputs
    .cio_ast_debug_out_o   (cio_sensor_ctrl_ast_debug_out_d2p),
    .cio_ast_debug_out_en_o(cio_sensor_ctrl_ast_debug_out_en_d2p),

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
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[34]),
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
    .EccCorrection(SramCtrlRetEccCorrection),
    .SecZeroInit(SecSramCtrlRetZeroInit)
  ) u_sram_ctrl_ret (
    // Clock and reset connections
    .clk_i(clkmgr_clocks.clk_io_div4_infra),
    .clk_otp_i(clkmgr_clocks.clk_io_div4_infra),
    .rst_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_otp_ni(rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),

    // alert_handler[34]: fatal_error
    .alert_tx_o(alert_tx_o[11]),
    .alert_rx_i(alert_rx_i[11]),

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


  // Pinmux connections
  // All muxed inputs
  assign cio_gpio_gpio_p2d_o[0] = mio_p2d[MioInGpioGpio0];
  assign cio_gpio_gpio_p2d_o[1] = mio_p2d[MioInGpioGpio1];
  assign cio_gpio_gpio_p2d_o[2] = mio_p2d[MioInGpioGpio2];
  assign cio_gpio_gpio_p2d_o[3] = mio_p2d[MioInGpioGpio3];
  assign cio_gpio_gpio_p2d_o[4] = mio_p2d[MioInGpioGpio4];
  assign cio_gpio_gpio_p2d_o[5] = mio_p2d[MioInGpioGpio5];
  assign cio_gpio_gpio_p2d_o[6] = mio_p2d[MioInGpioGpio6];
  assign cio_gpio_gpio_p2d_o[7] = mio_p2d[MioInGpioGpio7];
  assign cio_gpio_gpio_p2d_o[8] = mio_p2d[MioInGpioGpio8];
  assign cio_gpio_gpio_p2d_o[9] = mio_p2d[MioInGpioGpio9];
  assign cio_gpio_gpio_p2d_o[10] = mio_p2d[MioInGpioGpio10];
  assign cio_gpio_gpio_p2d_o[11] = mio_p2d[MioInGpioGpio11];
  assign cio_gpio_gpio_p2d_o[12] = mio_p2d[MioInGpioGpio12];
  assign cio_gpio_gpio_p2d_o[13] = mio_p2d[MioInGpioGpio13];
  assign cio_gpio_gpio_p2d_o[14] = mio_p2d[MioInGpioGpio14];
  assign cio_gpio_gpio_p2d_o[15] = mio_p2d[MioInGpioGpio15];
  assign cio_gpio_gpio_p2d_o[16] = mio_p2d[MioInGpioGpio16];
  assign cio_gpio_gpio_p2d_o[17] = mio_p2d[MioInGpioGpio17];
  assign cio_gpio_gpio_p2d_o[18] = mio_p2d[MioInGpioGpio18];
  assign cio_gpio_gpio_p2d_o[19] = mio_p2d[MioInGpioGpio19];
  assign cio_gpio_gpio_p2d_o[20] = mio_p2d[MioInGpioGpio20];
  assign cio_gpio_gpio_p2d_o[21] = mio_p2d[MioInGpioGpio21];
  assign cio_gpio_gpio_p2d_o[22] = mio_p2d[MioInGpioGpio22];
  assign cio_gpio_gpio_p2d_o[23] = mio_p2d[MioInGpioGpio23];
  assign cio_gpio_gpio_p2d_o[24] = mio_p2d[MioInGpioGpio24];
  assign cio_gpio_gpio_p2d_o[25] = mio_p2d[MioInGpioGpio25];
  assign cio_gpio_gpio_p2d_o[26] = mio_p2d[MioInGpioGpio26];
  assign cio_gpio_gpio_p2d_o[27] = mio_p2d[MioInGpioGpio27];
  assign cio_gpio_gpio_p2d_o[28] = mio_p2d[MioInGpioGpio28];
  assign cio_gpio_gpio_p2d_o[29] = mio_p2d[MioInGpioGpio29];
  assign cio_gpio_gpio_p2d_o[30] = mio_p2d[MioInGpioGpio30];
  assign cio_gpio_gpio_p2d_o[31] = mio_p2d[MioInGpioGpio31];
  assign cio_i2c0_sda_p2d_o = mio_p2d[MioInI2c0Sda];
  assign cio_i2c0_scl_p2d_o = mio_p2d[MioInI2c0Scl];
  assign cio_i2c1_sda_p2d_o = mio_p2d[MioInI2c1Sda];
  assign cio_i2c1_scl_p2d_o = mio_p2d[MioInI2c1Scl];
  assign cio_i2c2_sda_p2d_o = mio_p2d[MioInI2c2Sda];
  assign cio_i2c2_scl_p2d_o = mio_p2d[MioInI2c2Scl];
  assign cio_i3c0_scl_p2d_o = mio_p2d[MioInI3c0Scl];
  assign cio_i3c0_sda_p2d_o = mio_p2d[MioInI3c0Sda];
  assign cio_i3c1_scl_p2d_o = mio_p2d[MioInI3c1Scl];
  assign cio_i3c1_sda_p2d_o = mio_p2d[MioInI3c1Sda];
  assign cio_spi_host1_sd_p2d_o[0] = mio_p2d[MioInSpiHost1Sd0];
  assign cio_spi_host1_sd_p2d_o[1] = mio_p2d[MioInSpiHost1Sd1];
  assign cio_spi_host1_sd_p2d_o[2] = mio_p2d[MioInSpiHost1Sd2];
  assign cio_spi_host1_sd_p2d_o[3] = mio_p2d[MioInSpiHost1Sd3];
  assign cio_uart0_rx_p2d_o = mio_p2d[MioInUart0Rx];
  assign cio_uart1_rx_p2d_o = mio_p2d[MioInUart1Rx];
  assign cio_uart2_rx_p2d_o = mio_p2d[MioInUart2Rx];
  assign cio_uart3_rx_p2d_o = mio_p2d[MioInUart3Rx];
  assign cio_spi_device_tpm_csb_p2d_o = mio_p2d[MioInSpiDeviceTpmCsb];
  assign cio_rram_macro_tck_p2d_o = mio_p2d[MioInRramMacroTck];
  assign cio_rram_macro_tms_p2d_o = mio_p2d[MioInRramMacroTms];
  assign cio_rram_macro_tdi_p2d_o = mio_p2d[MioInRramMacroTdi];
  assign cio_sysrst_ctrl_ac_present_p2d = mio_p2d[MioInSysrstCtrlAcPresent];
  assign cio_sysrst_ctrl_key0_in_p2d = mio_p2d[MioInSysrstCtrlKey0In];
  assign cio_sysrst_ctrl_key1_in_p2d = mio_p2d[MioInSysrstCtrlKey1In];
  assign cio_sysrst_ctrl_key2_in_p2d = mio_p2d[MioInSysrstCtrlKey2In];
  assign cio_sysrst_ctrl_pwrb_in_p2d = mio_p2d[MioInSysrstCtrlPwrbIn];
  assign cio_sysrst_ctrl_lid_open_p2d = mio_p2d[MioInSysrstCtrlLidOpen];
  assign cio_usbdev_sense_p2d_o = mio_p2d[MioInUsbdevSense];

  // All muxed outputs
  assign mio_d2p[MioOutGpioGpio0] = cio_gpio_gpio_d2p_i[0];
  assign mio_d2p[MioOutGpioGpio1] = cio_gpio_gpio_d2p_i[1];
  assign mio_d2p[MioOutGpioGpio2] = cio_gpio_gpio_d2p_i[2];
  assign mio_d2p[MioOutGpioGpio3] = cio_gpio_gpio_d2p_i[3];
  assign mio_d2p[MioOutGpioGpio4] = cio_gpio_gpio_d2p_i[4];
  assign mio_d2p[MioOutGpioGpio5] = cio_gpio_gpio_d2p_i[5];
  assign mio_d2p[MioOutGpioGpio6] = cio_gpio_gpio_d2p_i[6];
  assign mio_d2p[MioOutGpioGpio7] = cio_gpio_gpio_d2p_i[7];
  assign mio_d2p[MioOutGpioGpio8] = cio_gpio_gpio_d2p_i[8];
  assign mio_d2p[MioOutGpioGpio9] = cio_gpio_gpio_d2p_i[9];
  assign mio_d2p[MioOutGpioGpio10] = cio_gpio_gpio_d2p_i[10];
  assign mio_d2p[MioOutGpioGpio11] = cio_gpio_gpio_d2p_i[11];
  assign mio_d2p[MioOutGpioGpio12] = cio_gpio_gpio_d2p_i[12];
  assign mio_d2p[MioOutGpioGpio13] = cio_gpio_gpio_d2p_i[13];
  assign mio_d2p[MioOutGpioGpio14] = cio_gpio_gpio_d2p_i[14];
  assign mio_d2p[MioOutGpioGpio15] = cio_gpio_gpio_d2p_i[15];
  assign mio_d2p[MioOutGpioGpio16] = cio_gpio_gpio_d2p_i[16];
  assign mio_d2p[MioOutGpioGpio17] = cio_gpio_gpio_d2p_i[17];
  assign mio_d2p[MioOutGpioGpio18] = cio_gpio_gpio_d2p_i[18];
  assign mio_d2p[MioOutGpioGpio19] = cio_gpio_gpio_d2p_i[19];
  assign mio_d2p[MioOutGpioGpio20] = cio_gpio_gpio_d2p_i[20];
  assign mio_d2p[MioOutGpioGpio21] = cio_gpio_gpio_d2p_i[21];
  assign mio_d2p[MioOutGpioGpio22] = cio_gpio_gpio_d2p_i[22];
  assign mio_d2p[MioOutGpioGpio23] = cio_gpio_gpio_d2p_i[23];
  assign mio_d2p[MioOutGpioGpio24] = cio_gpio_gpio_d2p_i[24];
  assign mio_d2p[MioOutGpioGpio25] = cio_gpio_gpio_d2p_i[25];
  assign mio_d2p[MioOutGpioGpio26] = cio_gpio_gpio_d2p_i[26];
  assign mio_d2p[MioOutGpioGpio27] = cio_gpio_gpio_d2p_i[27];
  assign mio_d2p[MioOutGpioGpio28] = cio_gpio_gpio_d2p_i[28];
  assign mio_d2p[MioOutGpioGpio29] = cio_gpio_gpio_d2p_i[29];
  assign mio_d2p[MioOutGpioGpio30] = cio_gpio_gpio_d2p_i[30];
  assign mio_d2p[MioOutGpioGpio31] = cio_gpio_gpio_d2p_i[31];
  assign mio_d2p[MioOutI2c0Sda] = cio_i2c0_sda_d2p_i;
  assign mio_d2p[MioOutI2c0Scl] = cio_i2c0_scl_d2p_i;
  assign mio_d2p[MioOutI2c1Sda] = cio_i2c1_sda_d2p_i;
  assign mio_d2p[MioOutI2c1Scl] = cio_i2c1_scl_d2p_i;
  assign mio_d2p[MioOutI2c2Sda] = cio_i2c2_sda_d2p_i;
  assign mio_d2p[MioOutI2c2Scl] = cio_i2c2_scl_d2p_i;
  assign mio_d2p[MioOutI3c0Scl] = cio_i3c0_scl_d2p_i;
  assign mio_d2p[MioOutI3c0Sda] = cio_i3c0_sda_d2p_i;
  assign mio_d2p[MioOutI3c1Scl] = cio_i3c1_scl_d2p_i;
  assign mio_d2p[MioOutI3c1Sda] = cio_i3c1_sda_d2p_i;
  assign mio_d2p[MioOutSpiHost1Sd0] = cio_spi_host1_sd_d2p_i[0];
  assign mio_d2p[MioOutSpiHost1Sd1] = cio_spi_host1_sd_d2p_i[1];
  assign mio_d2p[MioOutSpiHost1Sd2] = cio_spi_host1_sd_d2p_i[2];
  assign mio_d2p[MioOutSpiHost1Sd3] = cio_spi_host1_sd_d2p_i[3];
  assign mio_d2p[MioOutUart0Tx] = cio_uart0_tx_d2p_i;
  assign mio_d2p[MioOutUart1Tx] = cio_uart1_tx_d2p_i;
  assign mio_d2p[MioOutUart2Tx] = cio_uart2_tx_d2p_i;
  assign mio_d2p[MioOutUart3Tx] = cio_uart3_tx_d2p_i;
  assign mio_d2p[MioOutI3c0CtrlSclPu] = cio_i3c0_ctrl_scl_pu_d2p_i;
  assign mio_d2p[MioOutI3c0CtrlSdaPu] = cio_i3c0_ctrl_sda_pu_d2p_i;
  assign mio_d2p[MioOutI3c0SclHk] = cio_i3c0_scl_hk_d2p_i;
  assign mio_d2p[MioOutI3c0SdaHk] = cio_i3c0_sda_hk_d2p_i;
  assign mio_d2p[MioOutI3c1CtrlSclPu] = cio_i3c1_ctrl_scl_pu_d2p_i;
  assign mio_d2p[MioOutI3c1CtrlSdaPu] = cio_i3c1_ctrl_sda_pu_d2p_i;
  assign mio_d2p[MioOutI3c1SclHk] = cio_i3c1_scl_hk_d2p_i;
  assign mio_d2p[MioOutI3c1SdaHk] = cio_i3c1_sda_hk_d2p_i;
  assign mio_d2p[MioOutSpiHost1Sck] = cio_spi_host1_sck_d2p_i;
  assign mio_d2p[MioOutSpiHost1Csb] = cio_spi_host1_csb_d2p_i;
  assign mio_d2p[MioOutRramMacroTdo] = cio_rram_macro_tdo_d2p_i;
  assign mio_d2p[MioOutSensorCtrlAstDebugOut0] = cio_sensor_ctrl_ast_debug_out_d2p[0];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut1] = cio_sensor_ctrl_ast_debug_out_d2p[1];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut2] = cio_sensor_ctrl_ast_debug_out_d2p[2];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut3] = cio_sensor_ctrl_ast_debug_out_d2p[3];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut4] = cio_sensor_ctrl_ast_debug_out_d2p[4];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut5] = cio_sensor_ctrl_ast_debug_out_d2p[5];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut6] = cio_sensor_ctrl_ast_debug_out_d2p[6];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut7] = cio_sensor_ctrl_ast_debug_out_d2p[7];
  assign mio_d2p[MioOutSensorCtrlAstDebugOut8] = cio_sensor_ctrl_ast_debug_out_d2p[8];
  assign mio_d2p[MioOutSysrstCtrlBatDisable] = cio_sysrst_ctrl_bat_disable_d2p;
  assign mio_d2p[MioOutSysrstCtrlKey0Out] = cio_sysrst_ctrl_key0_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlKey1Out] = cio_sysrst_ctrl_key1_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlKey2Out] = cio_sysrst_ctrl_key2_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlPwrbOut] = cio_sysrst_ctrl_pwrb_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlZ3Wakeup] = cio_sysrst_ctrl_z3_wakeup_d2p;

  // All muxed output enables
  assign mio_en_d2p[MioOutGpioGpio0] = cio_gpio_gpio_en_d2p_i[0];
  assign mio_en_d2p[MioOutGpioGpio1] = cio_gpio_gpio_en_d2p_i[1];
  assign mio_en_d2p[MioOutGpioGpio2] = cio_gpio_gpio_en_d2p_i[2];
  assign mio_en_d2p[MioOutGpioGpio3] = cio_gpio_gpio_en_d2p_i[3];
  assign mio_en_d2p[MioOutGpioGpio4] = cio_gpio_gpio_en_d2p_i[4];
  assign mio_en_d2p[MioOutGpioGpio5] = cio_gpio_gpio_en_d2p_i[5];
  assign mio_en_d2p[MioOutGpioGpio6] = cio_gpio_gpio_en_d2p_i[6];
  assign mio_en_d2p[MioOutGpioGpio7] = cio_gpio_gpio_en_d2p_i[7];
  assign mio_en_d2p[MioOutGpioGpio8] = cio_gpio_gpio_en_d2p_i[8];
  assign mio_en_d2p[MioOutGpioGpio9] = cio_gpio_gpio_en_d2p_i[9];
  assign mio_en_d2p[MioOutGpioGpio10] = cio_gpio_gpio_en_d2p_i[10];
  assign mio_en_d2p[MioOutGpioGpio11] = cio_gpio_gpio_en_d2p_i[11];
  assign mio_en_d2p[MioOutGpioGpio12] = cio_gpio_gpio_en_d2p_i[12];
  assign mio_en_d2p[MioOutGpioGpio13] = cio_gpio_gpio_en_d2p_i[13];
  assign mio_en_d2p[MioOutGpioGpio14] = cio_gpio_gpio_en_d2p_i[14];
  assign mio_en_d2p[MioOutGpioGpio15] = cio_gpio_gpio_en_d2p_i[15];
  assign mio_en_d2p[MioOutGpioGpio16] = cio_gpio_gpio_en_d2p_i[16];
  assign mio_en_d2p[MioOutGpioGpio17] = cio_gpio_gpio_en_d2p_i[17];
  assign mio_en_d2p[MioOutGpioGpio18] = cio_gpio_gpio_en_d2p_i[18];
  assign mio_en_d2p[MioOutGpioGpio19] = cio_gpio_gpio_en_d2p_i[19];
  assign mio_en_d2p[MioOutGpioGpio20] = cio_gpio_gpio_en_d2p_i[20];
  assign mio_en_d2p[MioOutGpioGpio21] = cio_gpio_gpio_en_d2p_i[21];
  assign mio_en_d2p[MioOutGpioGpio22] = cio_gpio_gpio_en_d2p_i[22];
  assign mio_en_d2p[MioOutGpioGpio23] = cio_gpio_gpio_en_d2p_i[23];
  assign mio_en_d2p[MioOutGpioGpio24] = cio_gpio_gpio_en_d2p_i[24];
  assign mio_en_d2p[MioOutGpioGpio25] = cio_gpio_gpio_en_d2p_i[25];
  assign mio_en_d2p[MioOutGpioGpio26] = cio_gpio_gpio_en_d2p_i[26];
  assign mio_en_d2p[MioOutGpioGpio27] = cio_gpio_gpio_en_d2p_i[27];
  assign mio_en_d2p[MioOutGpioGpio28] = cio_gpio_gpio_en_d2p_i[28];
  assign mio_en_d2p[MioOutGpioGpio29] = cio_gpio_gpio_en_d2p_i[29];
  assign mio_en_d2p[MioOutGpioGpio30] = cio_gpio_gpio_en_d2p_i[30];
  assign mio_en_d2p[MioOutGpioGpio31] = cio_gpio_gpio_en_d2p_i[31];
  assign mio_en_d2p[MioOutI2c0Sda] = cio_i2c0_sda_en_d2p_i;
  assign mio_en_d2p[MioOutI2c0Scl] = cio_i2c0_scl_en_d2p_i;
  assign mio_en_d2p[MioOutI2c1Sda] = cio_i2c1_sda_en_d2p_i;
  assign mio_en_d2p[MioOutI2c1Scl] = cio_i2c1_scl_en_d2p_i;
  assign mio_en_d2p[MioOutI2c2Sda] = cio_i2c2_sda_en_d2p_i;
  assign mio_en_d2p[MioOutI2c2Scl] = cio_i2c2_scl_en_d2p_i;
  assign mio_en_d2p[MioOutI3c0Scl] = cio_i3c0_scl_en_d2p_i;
  assign mio_en_d2p[MioOutI3c0Sda] = cio_i3c0_sda_en_d2p_i;
  assign mio_en_d2p[MioOutI3c1Scl] = cio_i3c1_scl_en_d2p_i;
  assign mio_en_d2p[MioOutI3c1Sda] = cio_i3c1_sda_en_d2p_i;
  assign mio_en_d2p[MioOutSpiHost1Sd0] = cio_spi_host1_sd_en_d2p_i[0];
  assign mio_en_d2p[MioOutSpiHost1Sd1] = cio_spi_host1_sd_en_d2p_i[1];
  assign mio_en_d2p[MioOutSpiHost1Sd2] = cio_spi_host1_sd_en_d2p_i[2];
  assign mio_en_d2p[MioOutSpiHost1Sd3] = cio_spi_host1_sd_en_d2p_i[3];
  assign mio_en_d2p[MioOutUart0Tx] = cio_uart0_tx_en_d2p_i;
  assign mio_en_d2p[MioOutUart1Tx] = cio_uart1_tx_en_d2p_i;
  assign mio_en_d2p[MioOutUart2Tx] = cio_uart2_tx_en_d2p_i;
  assign mio_en_d2p[MioOutUart3Tx] = cio_uart3_tx_en_d2p_i;
  assign mio_en_d2p[MioOutI3c0CtrlSclPu] = cio_i3c0_ctrl_scl_pu_en_d2p_i;
  assign mio_en_d2p[MioOutI3c0CtrlSdaPu] = cio_i3c0_ctrl_sda_pu_en_d2p_i;
  assign mio_en_d2p[MioOutI3c0SclHk] = cio_i3c0_scl_hk_en_d2p_i;
  assign mio_en_d2p[MioOutI3c0SdaHk] = cio_i3c0_sda_hk_en_d2p_i;
  assign mio_en_d2p[MioOutI3c1CtrlSclPu] = cio_i3c1_ctrl_scl_pu_en_d2p_i;
  assign mio_en_d2p[MioOutI3c1CtrlSdaPu] = cio_i3c1_ctrl_sda_pu_en_d2p_i;
  assign mio_en_d2p[MioOutI3c1SclHk] = cio_i3c1_scl_hk_en_d2p_i;
  assign mio_en_d2p[MioOutI3c1SdaHk] = cio_i3c1_sda_hk_en_d2p_i;
  assign mio_en_d2p[MioOutSpiHost1Sck] = cio_spi_host1_sck_en_d2p_i;
  assign mio_en_d2p[MioOutSpiHost1Csb] = cio_spi_host1_csb_en_d2p_i;
  assign mio_en_d2p[MioOutRramMacroTdo] = cio_rram_macro_tdo_en_d2p_i;
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut0] = cio_sensor_ctrl_ast_debug_out_en_d2p[0];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut1] = cio_sensor_ctrl_ast_debug_out_en_d2p[1];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut2] = cio_sensor_ctrl_ast_debug_out_en_d2p[2];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut3] = cio_sensor_ctrl_ast_debug_out_en_d2p[3];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut4] = cio_sensor_ctrl_ast_debug_out_en_d2p[4];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut5] = cio_sensor_ctrl_ast_debug_out_en_d2p[5];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut6] = cio_sensor_ctrl_ast_debug_out_en_d2p[6];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut7] = cio_sensor_ctrl_ast_debug_out_en_d2p[7];
  assign mio_en_d2p[MioOutSensorCtrlAstDebugOut8] = cio_sensor_ctrl_ast_debug_out_en_d2p[8];
  assign mio_en_d2p[MioOutSysrstCtrlBatDisable] = cio_sysrst_ctrl_bat_disable_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlKey0Out] = cio_sysrst_ctrl_key0_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlKey1Out] = cio_sysrst_ctrl_key1_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlKey2Out] = cio_sysrst_ctrl_key2_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlPwrbOut] = cio_sysrst_ctrl_pwrb_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlZ3Wakeup] = cio_sysrst_ctrl_z3_wakeup_en_d2p;

  // All dedicated inputs
  logic [15:0] unused_dio_p2d;
  assign unused_dio_p2d = dio_p2d;
  assign cio_usbdev_usb_dp_p2d_o = dio_p2d[DioUsbdevUsbDp];
  assign cio_usbdev_usb_dn_p2d_o = dio_p2d[DioUsbdevUsbDn];
  assign cio_spi_host0_sd_p2d_o[0] = dio_p2d[DioSpiHost0Sd0];
  assign cio_spi_host0_sd_p2d_o[1] = dio_p2d[DioSpiHost0Sd1];
  assign cio_spi_host0_sd_p2d_o[2] = dio_p2d[DioSpiHost0Sd2];
  assign cio_spi_host0_sd_p2d_o[3] = dio_p2d[DioSpiHost0Sd3];
  assign cio_spi_device_sd_p2d_o[0] = dio_p2d[DioSpiDeviceSd0];
  assign cio_spi_device_sd_p2d_o[1] = dio_p2d[DioSpiDeviceSd1];
  assign cio_spi_device_sd_p2d_o[2] = dio_p2d[DioSpiDeviceSd2];
  assign cio_spi_device_sd_p2d_o[3] = dio_p2d[DioSpiDeviceSd3];
  assign cio_sysrst_ctrl_ec_rst_l_p2d = dio_p2d[DioSysrstCtrlEcRstL];
  assign cio_sysrst_ctrl_flash_wp_l_p2d = dio_p2d[DioSysrstCtrlFlashWpL];
  assign cio_spi_device_sck_p2d_o = dio_p2d[DioSpiDeviceSck];
  assign cio_spi_device_csb_p2d_o = dio_p2d[DioSpiDeviceCsb];

  // All dedicated outputs
  assign dio_d2p[DioUsbdevUsbDp] = cio_usbdev_usb_dp_d2p_i;
  assign dio_d2p[DioUsbdevUsbDn] = cio_usbdev_usb_dn_d2p_i;
  assign dio_d2p[DioSpiHost0Sd0] = cio_spi_host0_sd_d2p_i[0];
  assign dio_d2p[DioSpiHost0Sd1] = cio_spi_host0_sd_d2p_i[1];
  assign dio_d2p[DioSpiHost0Sd2] = cio_spi_host0_sd_d2p_i[2];
  assign dio_d2p[DioSpiHost0Sd3] = cio_spi_host0_sd_d2p_i[3];
  assign dio_d2p[DioSpiDeviceSd0] = cio_spi_device_sd_d2p_i[0];
  assign dio_d2p[DioSpiDeviceSd1] = cio_spi_device_sd_d2p_i[1];
  assign dio_d2p[DioSpiDeviceSd2] = cio_spi_device_sd_d2p_i[2];
  assign dio_d2p[DioSpiDeviceSd3] = cio_spi_device_sd_d2p_i[3];
  assign dio_d2p[DioSysrstCtrlEcRstL] = cio_sysrst_ctrl_ec_rst_l_d2p;
  assign dio_d2p[DioSysrstCtrlFlashWpL] = cio_sysrst_ctrl_flash_wp_l_d2p;
  assign dio_d2p[DioSpiDeviceSck] = 1'b0;
  assign dio_d2p[DioSpiDeviceCsb] = 1'b0;
  assign dio_d2p[DioSpiHost0Sck] = cio_spi_host0_sck_d2p_i;
  assign dio_d2p[DioSpiHost0Csb] = cio_spi_host0_csb_d2p_i;

  // All dedicated output enables
  assign dio_en_d2p[DioUsbdevUsbDp] = cio_usbdev_usb_dp_en_d2p_i;
  assign dio_en_d2p[DioUsbdevUsbDn] = cio_usbdev_usb_dn_en_d2p_i;
  assign dio_en_d2p[DioSpiHost0Sd0] = cio_spi_host0_sd_en_d2p_i[0];
  assign dio_en_d2p[DioSpiHost0Sd1] = cio_spi_host0_sd_en_d2p_i[1];
  assign dio_en_d2p[DioSpiHost0Sd2] = cio_spi_host0_sd_en_d2p_i[2];
  assign dio_en_d2p[DioSpiHost0Sd3] = cio_spi_host0_sd_en_d2p_i[3];
  assign dio_en_d2p[DioSpiDeviceSd0] = cio_spi_device_sd_en_d2p_i[0];
  assign dio_en_d2p[DioSpiDeviceSd1] = cio_spi_device_sd_en_d2p_i[1];
  assign dio_en_d2p[DioSpiDeviceSd2] = cio_spi_device_sd_en_d2p_i[2];
  assign dio_en_d2p[DioSpiDeviceSd3] = cio_spi_device_sd_en_d2p_i[3];
  assign dio_en_d2p[DioSysrstCtrlEcRstL] = cio_sysrst_ctrl_ec_rst_l_en_d2p;
  assign dio_en_d2p[DioSysrstCtrlFlashWpL] = cio_sysrst_ctrl_flash_wp_l_en_d2p;
  assign dio_en_d2p[DioSpiDeviceSck] = 1'b0;
  assign dio_en_d2p[DioSpiDeviceCsb] = 1'b0;
  assign dio_en_d2p[DioSpiHost0Sck] = cio_spi_host0_sck_en_d2p_i;
  assign dio_en_d2p[DioSpiHost0Csb] = cio_spi_host0_csb_en_d2p_i;

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

  // Struct breakout module tool-inserted DFT TAP signals
  pinmux_jtag_breakout u_dft_tap_breakout (
    .req_i    (pinmux_dft_jtag_req),
    .rsp_o    (pinmux_dft_jtag_rsp),
    .tck_o    (),
    .trst_no  (),
    .tms_o    (),
    .tdi_o    (),
    .tdo_i    (1'b0),
    .tdo_oe_i (1'b0)
  );

  // Make sure scanmode is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_o, ast_clk_src_sys_i, 0)

endmodule
