// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235

module top_earlgrey #(
  // Auto-inferred parameters
  parameter  OtpCtrlMemInitFile = "",
  parameter pinmux_pkg::target_cfg_t PinmuxAonTargetCfg = pinmux_pkg::DefaultTargetCfg,
  parameter bit SramCtrlRetAonInstrExec = 1,
  parameter logic [31:0] RvDmIdcodeValue = 32'h 0000_0001,
  parameter bit AesMasking = 1'b1,
  parameter aes_pkg::sbox_impl_e AesSBoxImpl = aes_pkg::SBoxImplDom,
  parameter int unsigned SecAesStartTriggerDelay = 0,
  parameter bit SecAesAllowForcingMasks = 1'b0,
  parameter bit SecAesSkipPRNGReseeding = 1'b0,
  parameter bit KmacEnMasking = 1,
  parameter int KmacReuseShare = 0,
  parameter aes_pkg::sbox_impl_e CsrngSBoxImpl = aes_pkg::SBoxImplCanright,
  parameter bit EntropySrcStub = 0,
  parameter bit SramCtrlMainInstrExec = 1,
  parameter bit OtbnStub = 0,
  parameter otbn_pkg::regfile_e OtbnRegFile = otbn_pkg::RegFileFF,
  parameter  RomCtrlBootRomInitFile = "",

  // Manually defined parameters
  parameter ibex_pkg::regfile_e IbexRegFile = ibex_pkg::RegFileFF,
  parameter bit IbexICache = 1,
  parameter bit IbexPipeLine = 0,
  parameter bit SecureIbex = 1
) (
  // Reset, clocks defined as part of intermodule
  input               rst_ni,

  // Multiplexed I/O
  input        [46:0] mio_in_i,
  output logic [46:0] mio_out_o,
  output logic [46:0] mio_oe_o,
  // Dedicated I/O
  input        [23:0] dio_in_i,
  output logic [23:0] dio_out_o,
  output logic [23:0] dio_oe_o,

  // pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,


  // Inter-module Signal External type
  output ast_pkg::adc_ast_req_t       adc_req_o,
  input  ast_pkg::adc_ast_rsp_t       adc_rsp_i,
  input  edn_pkg::edn_req_t       ast_edn_req_i,
  output edn_pkg::edn_rsp_t       ast_edn_rsp_o,
  output lc_ctrl_pkg::lc_tx_t       ast_lc_dft_en_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_t       ram_1p_cfg_i,
  input  prim_ram_2p_pkg::ram_2p_cfg_t       ram_2p_cfg_i,
  input  prim_rom_pkg::rom_cfg_t       rom_cfg_i,
  input  logic       clk_main_i,
  input  logic       clk_io_i,
  input  logic       clk_usb_i,
  input  logic       clk_aon_i,
  output logic       clk_main_jitter_en_o,
  output lc_ctrl_pkg::lc_tx_t       ast_clk_byp_req_o,
  input  lc_ctrl_pkg::lc_tx_t       ast_clk_byp_ack_i,
  output ast_pkg::ast_dif_t       flash_alert_o,
  input  lc_ctrl_pkg::lc_tx_t       flash_bist_enable_i,
  input  logic       flash_power_down_h_i,
  input  logic       flash_power_ready_h_i,
  output entropy_src_pkg::entropy_src_rng_req_t       es_rng_req_o,
  input  entropy_src_pkg::entropy_src_rng_rsp_t       es_rng_rsp_i,
  output logic       es_rng_fips_o,
  output tlul_pkg::tl_h2d_t       ast_tl_req_o,
  input  tlul_pkg::tl_d2h_t       ast_tl_rsp_i,
  output pinmux_pkg::dft_strap_test_req_t       dft_strap_test_o,
  input  logic       dft_hold_tap_sel_i,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_ast_rsp_i,
  output otp_ctrl_pkg::otp_ast_req_t       otp_ctrl_otp_ast_pwr_seq_o,
  input  otp_ctrl_pkg::otp_ast_rsp_t       otp_ctrl_otp_ast_pwr_seq_h_i,
  output ast_pkg::ast_dif_t       otp_alert_o,
  input  ast_pkg::ast_alert_req_t       sensor_ctrl_ast_alert_req_i,
  output ast_pkg::ast_alert_rsp_t       sensor_ctrl_ast_alert_rsp_o,
  input  ast_pkg::ast_status_t       sensor_ctrl_ast_status_i,
  input  logic [8:0] ast2pinmux_i,
  input  logic       ast_init_done_i,
  output logic       usbdev_usb_ref_val_o,
  output logic       usbdev_usb_ref_pulse_o,
  output clkmgr_pkg::clkmgr_ast_out_t       clks_ast_o,
  output rstmgr_pkg::rstmgr_ast_out_t       rsts_ast_o,

  // Flash specific voltages
  inout [1:0] flash_test_mode_a_io,
  inout flash_test_voltage_h_io,

  // OTP specific voltages
  inout otp_ext_voltage_h_io,

  input                      scan_rst_ni, // reset used for test mode
  input                      scan_en_i,
  input lc_ctrl_pkg::lc_tx_t scanmode_i   // lc_ctrl_pkg::On for Scan
);

  // JTAG IDCODE for development versions of this code.
  // Manufacturers of OpenTitan chips must replace this code with one of their
  // own IDs.
  // Field structure as defined in the IEEE 1149.1 (JTAG) specification,
  // section 12.1.1.
  localparam logic [31:0] JTAG_IDCODE = {
    4'h0,     // Version
    16'h4F54, // Part Number: "OT"
    11'h426,  // Manufacturer Identity: Google
    1'b1      // (fixed)
  };

  import tlul_pkg::*;
  import top_pkg::*;
  import tl_main_pkg::*;
  import top_earlgrey_pkg::*;
  // Compile-time random constants
  import top_earlgrey_rnd_cnst_pkg::*;

  // Signals
  logic [55:0] mio_p2d;
  logic [72:0] mio_d2p;
  logic [72:0] mio_en_d2p;
  logic [23:0] dio_p2d;
  logic [23:0] dio_d2p;
  logic [23:0] dio_en_d2p;
  // uart0
  logic        cio_uart0_rx_p2d;
  logic        cio_uart0_tx_d2p;
  logic        cio_uart0_tx_en_d2p;
  // uart1
  logic        cio_uart1_rx_p2d;
  logic        cio_uart1_tx_d2p;
  logic        cio_uart1_tx_en_d2p;
  // uart2
  logic        cio_uart2_rx_p2d;
  logic        cio_uart2_tx_d2p;
  logic        cio_uart2_tx_en_d2p;
  // uart3
  logic        cio_uart3_rx_p2d;
  logic        cio_uart3_tx_d2p;
  logic        cio_uart3_tx_en_d2p;
  // gpio
  logic [31:0] cio_gpio_gpio_p2d;
  logic [31:0] cio_gpio_gpio_d2p;
  logic [31:0] cio_gpio_gpio_en_d2p;
  // spi_device
  logic        cio_spi_device_sck_p2d;
  logic        cio_spi_device_csb_p2d;
  logic [3:0]  cio_spi_device_sd_p2d;
  logic [3:0]  cio_spi_device_sd_d2p;
  logic [3:0]  cio_spi_device_sd_en_d2p;
  // spi_host0
  logic [3:0]  cio_spi_host0_sd_p2d;
  logic        cio_spi_host0_sck_d2p;
  logic        cio_spi_host0_sck_en_d2p;
  logic        cio_spi_host0_csb_d2p;
  logic        cio_spi_host0_csb_en_d2p;
  logic [3:0]  cio_spi_host0_sd_d2p;
  logic [3:0]  cio_spi_host0_sd_en_d2p;
  // spi_host1
  logic [3:0]  cio_spi_host1_sd_p2d;
  logic        cio_spi_host1_sck_d2p;
  logic        cio_spi_host1_sck_en_d2p;
  logic        cio_spi_host1_csb_d2p;
  logic        cio_spi_host1_csb_en_d2p;
  logic [3:0]  cio_spi_host1_sd_d2p;
  logic [3:0]  cio_spi_host1_sd_en_d2p;
  // i2c0
  logic        cio_i2c0_sda_p2d;
  logic        cio_i2c0_scl_p2d;
  logic        cio_i2c0_sda_d2p;
  logic        cio_i2c0_sda_en_d2p;
  logic        cio_i2c0_scl_d2p;
  logic        cio_i2c0_scl_en_d2p;
  // i2c1
  logic        cio_i2c1_sda_p2d;
  logic        cio_i2c1_scl_p2d;
  logic        cio_i2c1_sda_d2p;
  logic        cio_i2c1_sda_en_d2p;
  logic        cio_i2c1_scl_d2p;
  logic        cio_i2c1_scl_en_d2p;
  // i2c2
  logic        cio_i2c2_sda_p2d;
  logic        cio_i2c2_scl_p2d;
  logic        cio_i2c2_sda_d2p;
  logic        cio_i2c2_sda_en_d2p;
  logic        cio_i2c2_scl_d2p;
  logic        cio_i2c2_scl_en_d2p;
  // pattgen
  logic        cio_pattgen_pda0_tx_d2p;
  logic        cio_pattgen_pda0_tx_en_d2p;
  logic        cio_pattgen_pcl0_tx_d2p;
  logic        cio_pattgen_pcl0_tx_en_d2p;
  logic        cio_pattgen_pda1_tx_d2p;
  logic        cio_pattgen_pda1_tx_en_d2p;
  logic        cio_pattgen_pcl1_tx_d2p;
  logic        cio_pattgen_pcl1_tx_en_d2p;
  // rv_timer
  // usbdev
  logic        cio_usbdev_sense_p2d;
  logic        cio_usbdev_d_p2d;
  logic        cio_usbdev_dp_p2d;
  logic        cio_usbdev_dn_p2d;
  logic        cio_usbdev_se0_d2p;
  logic        cio_usbdev_se0_en_d2p;
  logic        cio_usbdev_dp_pullup_d2p;
  logic        cio_usbdev_dp_pullup_en_d2p;
  logic        cio_usbdev_dn_pullup_d2p;
  logic        cio_usbdev_dn_pullup_en_d2p;
  logic        cio_usbdev_tx_mode_se_d2p;
  logic        cio_usbdev_tx_mode_se_en_d2p;
  logic        cio_usbdev_suspend_d2p;
  logic        cio_usbdev_suspend_en_d2p;
  logic        cio_usbdev_rx_enable_d2p;
  logic        cio_usbdev_rx_enable_en_d2p;
  logic        cio_usbdev_d_d2p;
  logic        cio_usbdev_d_en_d2p;
  logic        cio_usbdev_dp_d2p;
  logic        cio_usbdev_dp_en_d2p;
  logic        cio_usbdev_dn_d2p;
  logic        cio_usbdev_dn_en_d2p;
  // otp_ctrl
  // lc_ctrl
  // alert_handler
  // pwrmgr_aon
  // rstmgr_aon
  // clkmgr_aon
  // sysrst_ctrl_aon
  logic        cio_sysrst_ctrl_aon_ac_present_p2d;
  logic        cio_sysrst_ctrl_aon_ec_rst_in_l_p2d;
  logic        cio_sysrst_ctrl_aon_key0_in_p2d;
  logic        cio_sysrst_ctrl_aon_key1_in_p2d;
  logic        cio_sysrst_ctrl_aon_key2_in_p2d;
  logic        cio_sysrst_ctrl_aon_pwrb_in_p2d;
  logic        cio_sysrst_ctrl_aon_lid_open_p2d;
  logic        cio_sysrst_ctrl_aon_bat_disable_d2p;
  logic        cio_sysrst_ctrl_aon_bat_disable_en_d2p;
  logic        cio_sysrst_ctrl_aon_ec_rst_out_l_d2p;
  logic        cio_sysrst_ctrl_aon_ec_rst_out_l_en_d2p;
  logic        cio_sysrst_ctrl_aon_key0_out_d2p;
  logic        cio_sysrst_ctrl_aon_key0_out_en_d2p;
  logic        cio_sysrst_ctrl_aon_key1_out_d2p;
  logic        cio_sysrst_ctrl_aon_key1_out_en_d2p;
  logic        cio_sysrst_ctrl_aon_key2_out_d2p;
  logic        cio_sysrst_ctrl_aon_key2_out_en_d2p;
  logic        cio_sysrst_ctrl_aon_pwrb_out_d2p;
  logic        cio_sysrst_ctrl_aon_pwrb_out_en_d2p;
  logic        cio_sysrst_ctrl_aon_z3_wakeup_d2p;
  logic        cio_sysrst_ctrl_aon_z3_wakeup_en_d2p;
  // adc_ctrl_aon
  // pwm_aon
  logic [5:0]  cio_pwm_aon_pwm_d2p;
  logic [5:0]  cio_pwm_aon_pwm_en_d2p;
  // pinmux_aon
  // aon_timer_aon
  // sensor_ctrl_aon
  logic [8:0]  cio_sensor_ctrl_aon_ast_debug_out_d2p;
  logic [8:0]  cio_sensor_ctrl_aon_ast_debug_out_en_d2p;
  // sram_ctrl_ret_aon
  // flash_ctrl
  logic        cio_flash_ctrl_tck_p2d;
  logic        cio_flash_ctrl_tms_p2d;
  logic        cio_flash_ctrl_tdi_p2d;
  logic        cio_flash_ctrl_tdo_d2p;
  logic        cio_flash_ctrl_tdo_en_d2p;
  // rv_dm
  // rv_plic
  // aes
  // hmac
  // kmac
  // keymgr
  // csrng
  // entropy_src
  // edn0
  // edn1
  // sram_ctrl_main
  // otbn
  // rom_ctrl
  // rv_core_ibex_peri


  logic [179:0]  intr_vector;
  // Interrupt source list
  logic intr_uart0_tx_watermark;
  logic intr_uart0_rx_watermark;
  logic intr_uart0_tx_empty;
  logic intr_uart0_rx_overflow;
  logic intr_uart0_rx_frame_err;
  logic intr_uart0_rx_break_err;
  logic intr_uart0_rx_timeout;
  logic intr_uart0_rx_parity_err;
  logic intr_uart1_tx_watermark;
  logic intr_uart1_rx_watermark;
  logic intr_uart1_tx_empty;
  logic intr_uart1_rx_overflow;
  logic intr_uart1_rx_frame_err;
  logic intr_uart1_rx_break_err;
  logic intr_uart1_rx_timeout;
  logic intr_uart1_rx_parity_err;
  logic intr_uart2_tx_watermark;
  logic intr_uart2_rx_watermark;
  logic intr_uart2_tx_empty;
  logic intr_uart2_rx_overflow;
  logic intr_uart2_rx_frame_err;
  logic intr_uart2_rx_break_err;
  logic intr_uart2_rx_timeout;
  logic intr_uart2_rx_parity_err;
  logic intr_uart3_tx_watermark;
  logic intr_uart3_rx_watermark;
  logic intr_uart3_tx_empty;
  logic intr_uart3_rx_overflow;
  logic intr_uart3_rx_frame_err;
  logic intr_uart3_rx_break_err;
  logic intr_uart3_rx_timeout;
  logic intr_uart3_rx_parity_err;
  logic [31:0] intr_gpio_gpio;
  logic intr_spi_device_rxf;
  logic intr_spi_device_rxlvl;
  logic intr_spi_device_txlvl;
  logic intr_spi_device_rxerr;
  logic intr_spi_device_rxoverflow;
  logic intr_spi_device_txunderflow;
  logic intr_spi_host0_error;
  logic intr_spi_host0_spi_event;
  logic intr_spi_host1_error;
  logic intr_spi_host1_spi_event;
  logic intr_i2c0_fmt_watermark;
  logic intr_i2c0_rx_watermark;
  logic intr_i2c0_fmt_overflow;
  logic intr_i2c0_rx_overflow;
  logic intr_i2c0_nak;
  logic intr_i2c0_scl_interference;
  logic intr_i2c0_sda_interference;
  logic intr_i2c0_stretch_timeout;
  logic intr_i2c0_sda_unstable;
  logic intr_i2c0_trans_complete;
  logic intr_i2c0_tx_empty;
  logic intr_i2c0_tx_nonempty;
  logic intr_i2c0_tx_overflow;
  logic intr_i2c0_acq_overflow;
  logic intr_i2c0_ack_stop;
  logic intr_i2c0_host_timeout;
  logic intr_i2c1_fmt_watermark;
  logic intr_i2c1_rx_watermark;
  logic intr_i2c1_fmt_overflow;
  logic intr_i2c1_rx_overflow;
  logic intr_i2c1_nak;
  logic intr_i2c1_scl_interference;
  logic intr_i2c1_sda_interference;
  logic intr_i2c1_stretch_timeout;
  logic intr_i2c1_sda_unstable;
  logic intr_i2c1_trans_complete;
  logic intr_i2c1_tx_empty;
  logic intr_i2c1_tx_nonempty;
  logic intr_i2c1_tx_overflow;
  logic intr_i2c1_acq_overflow;
  logic intr_i2c1_ack_stop;
  logic intr_i2c1_host_timeout;
  logic intr_i2c2_fmt_watermark;
  logic intr_i2c2_rx_watermark;
  logic intr_i2c2_fmt_overflow;
  logic intr_i2c2_rx_overflow;
  logic intr_i2c2_nak;
  logic intr_i2c2_scl_interference;
  logic intr_i2c2_sda_interference;
  logic intr_i2c2_stretch_timeout;
  logic intr_i2c2_sda_unstable;
  logic intr_i2c2_trans_complete;
  logic intr_i2c2_tx_empty;
  logic intr_i2c2_tx_nonempty;
  logic intr_i2c2_tx_overflow;
  logic intr_i2c2_acq_overflow;
  logic intr_i2c2_ack_stop;
  logic intr_i2c2_host_timeout;
  logic intr_pattgen_done_ch0;
  logic intr_pattgen_done_ch1;
  logic intr_rv_timer_timer_expired_0_0;
  logic intr_usbdev_pkt_received;
  logic intr_usbdev_pkt_sent;
  logic intr_usbdev_disconnected;
  logic intr_usbdev_host_lost;
  logic intr_usbdev_link_reset;
  logic intr_usbdev_link_suspend;
  logic intr_usbdev_link_resume;
  logic intr_usbdev_av_empty;
  logic intr_usbdev_rx_full;
  logic intr_usbdev_av_overflow;
  logic intr_usbdev_link_in_err;
  logic intr_usbdev_rx_crc_err;
  logic intr_usbdev_rx_pid_err;
  logic intr_usbdev_rx_bitstuff_err;
  logic intr_usbdev_frame;
  logic intr_usbdev_connected;
  logic intr_usbdev_link_out_err;
  logic intr_otp_ctrl_otp_operation_done;
  logic intr_otp_ctrl_otp_error;
  logic intr_alert_handler_classa;
  logic intr_alert_handler_classb;
  logic intr_alert_handler_classc;
  logic intr_alert_handler_classd;
  logic intr_pwrmgr_aon_wakeup;
  logic intr_sysrst_ctrl_aon_sysrst_ctrl;
  logic intr_adc_ctrl_aon_debug_cable;
  logic intr_aon_timer_aon_wkup_timer_expired;
  logic intr_aon_timer_aon_wdog_timer_bark;
  logic intr_flash_ctrl_prog_empty;
  logic intr_flash_ctrl_prog_lvl;
  logic intr_flash_ctrl_rd_full;
  logic intr_flash_ctrl_rd_lvl;
  logic intr_flash_ctrl_op_done;
  logic intr_flash_ctrl_err;
  logic intr_hmac_hmac_done;
  logic intr_hmac_fifo_empty;
  logic intr_hmac_hmac_err;
  logic intr_kmac_kmac_done;
  logic intr_kmac_fifo_empty;
  logic intr_kmac_kmac_err;
  logic intr_keymgr_op_done;
  logic intr_csrng_cs_cmd_req_done;
  logic intr_csrng_cs_entropy_req;
  logic intr_csrng_cs_hw_inst_exc;
  logic intr_csrng_cs_fatal_err;
  logic intr_entropy_src_es_entropy_valid;
  logic intr_entropy_src_es_health_test_failed;
  logic intr_entropy_src_es_observe_fifo_ready;
  logic intr_entropy_src_es_fatal_err;
  logic intr_edn0_edn_cmd_req_done;
  logic intr_edn0_edn_fatal_err;
  logic intr_edn1_edn_cmd_req_done;
  logic intr_edn1_edn_fatal_err;
  logic intr_otbn_done;



  logic [0:0] irq_plic;
  logic [0:0] msip;
  logic [7:0] irq_id[1];
  logic [7:0] unused_irq_id[1];

  // this avoids lint errors
  assign unused_irq_id = irq_id;

  // Alert list
  prim_alert_pkg::alert_tx_t [alert_pkg::NAlerts-1:0]  alert_tx;
  prim_alert_pkg::alert_rx_t [alert_pkg::NAlerts-1:0]  alert_rx;


  // define inter-module signals
  prim_ram_1p_pkg::ram_1p_cfg_t       ast_ram_1p_cfg;
  prim_ram_2p_pkg::ram_2p_cfg_t       ast_ram_2p_cfg;
  prim_rom_pkg::rom_cfg_t       ast_rom_cfg;
  alert_pkg::alert_crashdump_t       alert_handler_crashdump;
  prim_esc_pkg::esc_rx_t [3:0] alert_handler_esc_rx;
  prim_esc_pkg::esc_tx_t [3:0] alert_handler_esc_tx;
  csrng_pkg::csrng_req_t [1:0] csrng_csrng_cmd_req;
  csrng_pkg::csrng_rsp_t [1:0] csrng_csrng_cmd_rsp;
  entropy_src_pkg::entropy_src_hw_if_req_t       csrng_entropy_src_hw_if_req;
  entropy_src_pkg::entropy_src_hw_if_rsp_t       csrng_entropy_src_hw_if_rsp;
  entropy_src_pkg::cs_aes_halt_req_t       csrng_cs_aes_halt_req;
  entropy_src_pkg::cs_aes_halt_rsp_t       csrng_cs_aes_halt_rsp;
  flash_ctrl_pkg::flash_req_t       flash_ctrl_flash_req;
  flash_ctrl_pkg::flash_rsp_t       flash_ctrl_flash_rsp;
  flash_ctrl_pkg::keymgr_flash_t       flash_ctrl_keymgr;
  otp_ctrl_pkg::flash_otp_key_req_t       flash_ctrl_otp_req;
  otp_ctrl_pkg::flash_otp_key_rsp_t       flash_ctrl_otp_rsp;
  lc_ctrl_pkg::lc_tx_t       flash_ctrl_rma_req;
  lc_ctrl_pkg::lc_tx_t       flash_ctrl_rma_ack;
  lc_ctrl_pkg::lc_flash_rma_seed_t       flash_ctrl_rma_seed;
  otp_ctrl_pkg::sram_otp_key_req_t [1:0] otp_ctrl_sram_otp_key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t [1:0] otp_ctrl_sram_otp_key_rsp;
  pwrmgr_pkg::pwr_flash_t       pwrmgr_aon_pwr_flash;
  pwrmgr_pkg::pwr_rst_req_t       pwrmgr_aon_pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t       pwrmgr_aon_pwr_rst_rsp;
  pwrmgr_pkg::pwr_clk_req_t       pwrmgr_aon_pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t       pwrmgr_aon_pwr_clk_rsp;
  pwrmgr_pkg::pwr_otp_req_t       pwrmgr_aon_pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_aon_pwr_otp_rsp;
  pwrmgr_pkg::pwr_lc_req_t       pwrmgr_aon_pwr_lc_req;
  pwrmgr_pkg::pwr_lc_rsp_t       pwrmgr_aon_pwr_lc_rsp;
  logic       pwrmgr_aon_strap;
  logic       pwrmgr_aon_low_power;
  rom_ctrl_pkg::pwrmgr_data_t       rom_ctrl_pwrmgr_data;
  rom_ctrl_pkg::keymgr_data_t       rom_ctrl_keymgr_data;
  ibex_pkg::crash_dump_t       rv_core_ibex_crash_dump;
  logic       usbdev_usb_out_of_rst;
  logic       usbdev_usb_aon_wake_en;
  logic       usbdev_usb_aon_wake_ack;
  logic       usbdev_usb_suspend;
  usbdev_pkg::awk_state_t       pinmux_aon_usb_state_debug;
  edn_pkg::edn_req_t [6:0] edn0_edn_req;
  edn_pkg::edn_rsp_t [6:0] edn0_edn_rsp;
  edn_pkg::edn_req_t [6:0] edn1_edn_req;
  edn_pkg::edn_rsp_t [6:0] edn1_edn_rsp;
  otp_ctrl_pkg::otbn_otp_key_req_t       otp_ctrl_otbn_otp_key_req;
  otp_ctrl_pkg::otbn_otp_key_rsp_t       otp_ctrl_otbn_otp_key_rsp;
  otp_ctrl_pkg::otp_keymgr_key_t       otp_ctrl_otp_keymgr_key;
  keymgr_pkg::hw_key_req_t       keymgr_kmac_key;
  kmac_pkg::app_req_t [2:0] kmac_app_req;
  kmac_pkg::app_rsp_t [2:0] kmac_app_rsp;
  logic [4:0] clkmgr_aon_idle;
  jtag_pkg::jtag_req_t       pinmux_aon_lc_jtag_req;
  jtag_pkg::jtag_rsp_t       pinmux_aon_lc_jtag_rsp;
  jtag_pkg::jtag_req_t       pinmux_aon_rv_jtag_req;
  jtag_pkg::jtag_rsp_t       pinmux_aon_rv_jtag_rsp;
  otp_ctrl_pkg::otp_lc_data_t       otp_ctrl_otp_lc_data;
  otp_ctrl_pkg::lc_otp_program_req_t       lc_ctrl_lc_otp_program_req;
  otp_ctrl_pkg::lc_otp_program_rsp_t       lc_ctrl_lc_otp_program_rsp;
  lc_ctrl_pkg::lc_keymgr_div_t       lc_ctrl_lc_keymgr_div;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_nvm_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_cpu_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_keymgr_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_check_byp_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_ack;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_creator_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_owner_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_iso_part_sw_rd_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_iso_part_sw_wr_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_seed_hw_rd_en;
  rv_core_ibex_peri_pkg::alert_event_t       rv_core_ibex_fatal_intg_event;
  rv_core_ibex_peri_pkg::alert_event_t       rv_core_ibex_fatal_core_event;
  rv_core_ibex_peri_pkg::alert_event_t       rv_core_ibex_recov_core_event;
  rv_core_ibex_peri_pkg::region_cfg_t [1:0] rv_core_ibex_peri_ibus_region_cfg;
  rv_core_ibex_peri_pkg::region_cfg_t [1:0] rv_core_ibex_peri_dbus_region_cfg;
  spi_device_pkg::passthrough_req_t       spi_device_passthrough_req;
  spi_device_pkg::passthrough_rsp_t       spi_device_passthrough_rsp;
  logic       rv_dm_ndmreset_req;
  logic [4:0] pwrmgr_aon_wakeups;
  logic [1:0] pwrmgr_aon_rstreqs;
  tlul_pkg::tl_h2d_t       main_tl_rv_dm__sba_req;
  tlul_pkg::tl_d2h_t       main_tl_rv_dm__sba_rsp;
  tlul_pkg::tl_h2d_t       rv_dm_regs_tl_d_req;
  tlul_pkg::tl_d2h_t       rv_dm_regs_tl_d_rsp;
  tlul_pkg::tl_h2d_t       rv_dm_rom_tl_d_req;
  tlul_pkg::tl_d2h_t       rv_dm_rom_tl_d_rsp;
  tlul_pkg::tl_h2d_t       rom_ctrl_rom_tl_req;
  tlul_pkg::tl_d2h_t       rom_ctrl_rom_tl_rsp;
  tlul_pkg::tl_h2d_t       rom_ctrl_regs_tl_req;
  tlul_pkg::tl_d2h_t       rom_ctrl_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       eflash_tl_req;
  tlul_pkg::tl_d2h_t       eflash_tl_rsp;
  tlul_pkg::tl_h2d_t       main_tl_peri_req;
  tlul_pkg::tl_d2h_t       main_tl_peri_rsp;
  tlul_pkg::tl_h2d_t       flash_ctrl_core_tl_req;
  tlul_pkg::tl_d2h_t       flash_ctrl_core_tl_rsp;
  tlul_pkg::tl_h2d_t       flash_ctrl_prim_tl_req;
  tlul_pkg::tl_d2h_t       flash_ctrl_prim_tl_rsp;
  tlul_pkg::tl_h2d_t       hmac_tl_req;
  tlul_pkg::tl_d2h_t       hmac_tl_rsp;
  tlul_pkg::tl_h2d_t       kmac_tl_req;
  tlul_pkg::tl_d2h_t       kmac_tl_rsp;
  tlul_pkg::tl_h2d_t       aes_tl_req;
  tlul_pkg::tl_d2h_t       aes_tl_rsp;
  tlul_pkg::tl_h2d_t       entropy_src_tl_req;
  tlul_pkg::tl_d2h_t       entropy_src_tl_rsp;
  tlul_pkg::tl_h2d_t       csrng_tl_req;
  tlul_pkg::tl_d2h_t       csrng_tl_rsp;
  tlul_pkg::tl_h2d_t       edn0_tl_req;
  tlul_pkg::tl_d2h_t       edn0_tl_rsp;
  tlul_pkg::tl_h2d_t       edn1_tl_req;
  tlul_pkg::tl_d2h_t       edn1_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_plic_tl_req;
  tlul_pkg::tl_d2h_t       rv_plic_tl_rsp;
  tlul_pkg::tl_h2d_t       otbn_tl_req;
  tlul_pkg::tl_d2h_t       otbn_tl_rsp;
  tlul_pkg::tl_h2d_t       keymgr_tl_req;
  tlul_pkg::tl_d2h_t       keymgr_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_core_ibex_peri_tl_req;
  tlul_pkg::tl_d2h_t       rv_core_ibex_peri_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_main_regs_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_main_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_main_ram_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_main_ram_tl_rsp;
  tlul_pkg::tl_h2d_t       uart0_tl_req;
  tlul_pkg::tl_d2h_t       uart0_tl_rsp;
  tlul_pkg::tl_h2d_t       uart1_tl_req;
  tlul_pkg::tl_d2h_t       uart1_tl_rsp;
  tlul_pkg::tl_h2d_t       uart2_tl_req;
  tlul_pkg::tl_d2h_t       uart2_tl_rsp;
  tlul_pkg::tl_h2d_t       uart3_tl_req;
  tlul_pkg::tl_d2h_t       uart3_tl_rsp;
  tlul_pkg::tl_h2d_t       i2c0_tl_req;
  tlul_pkg::tl_d2h_t       i2c0_tl_rsp;
  tlul_pkg::tl_h2d_t       i2c1_tl_req;
  tlul_pkg::tl_d2h_t       i2c1_tl_rsp;
  tlul_pkg::tl_h2d_t       i2c2_tl_req;
  tlul_pkg::tl_d2h_t       i2c2_tl_rsp;
  tlul_pkg::tl_h2d_t       pattgen_tl_req;
  tlul_pkg::tl_d2h_t       pattgen_tl_rsp;
  tlul_pkg::tl_h2d_t       pwm_aon_tl_req;
  tlul_pkg::tl_d2h_t       pwm_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       gpio_tl_req;
  tlul_pkg::tl_d2h_t       gpio_tl_rsp;
  tlul_pkg::tl_h2d_t       spi_device_tl_req;
  tlul_pkg::tl_d2h_t       spi_device_tl_rsp;
  tlul_pkg::tl_h2d_t       spi_host0_tl_req;
  tlul_pkg::tl_d2h_t       spi_host0_tl_rsp;
  tlul_pkg::tl_h2d_t       spi_host1_tl_req;
  tlul_pkg::tl_d2h_t       spi_host1_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_timer_tl_req;
  tlul_pkg::tl_d2h_t       rv_timer_tl_rsp;
  tlul_pkg::tl_h2d_t       usbdev_tl_req;
  tlul_pkg::tl_d2h_t       usbdev_tl_rsp;
  tlul_pkg::tl_h2d_t       pwrmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       pwrmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       rstmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       rstmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       clkmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       clkmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       pinmux_aon_tl_req;
  tlul_pkg::tl_d2h_t       pinmux_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       otp_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       otp_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       lc_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       lc_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       sensor_ctrl_aon_tl_req;
  tlul_pkg::tl_d2h_t       sensor_ctrl_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       alert_handler_tl_req;
  tlul_pkg::tl_d2h_t       alert_handler_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_regs_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_ram_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_ram_tl_rsp;
  tlul_pkg::tl_h2d_t       aon_timer_aon_tl_req;
  tlul_pkg::tl_d2h_t       aon_timer_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       sysrst_ctrl_aon_tl_req;
  tlul_pkg::tl_d2h_t       sysrst_ctrl_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       adc_ctrl_aon_tl_req;
  tlul_pkg::tl_d2h_t       adc_ctrl_aon_tl_rsp;
  rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets;
  logic       rstmgr_aon_rst_cpu_n;
  pwrmgr_pkg::pwr_cpu_t       pwrmgr_aon_pwr_cpu;
  lc_ctrl_pkg::lc_tx_t       pwrmgr_aon_fetch_en;
  clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks;
  logic       rv_dm_debug_req;
  tlul_pkg::tl_h2d_t       main_tl_corei_req;
  tlul_pkg::tl_d2h_t       main_tl_corei_rsp;
  tlul_pkg::tl_h2d_t       main_tl_cored_req;
  tlul_pkg::tl_d2h_t       main_tl_cored_rsp;
  jtag_pkg::jtag_req_t       pinmux_aon_dft_jtag_req;
  jtag_pkg::jtag_rsp_t       pinmux_aon_dft_jtag_rsp;
  otp_ctrl_part_pkg::otp_hw_cfg_t       otp_ctrl_otp_hw_cfg;
  otp_ctrl_pkg::otp_en_t       csrng_otp_en_csrng_sw_app_read;
  otp_ctrl_pkg::otp_en_t       entropy_src_otp_en_entropy_src_fw_read;
  otp_ctrl_pkg::otp_en_t       entropy_src_otp_en_entropy_src_fw_over;
  otp_ctrl_pkg::otp_device_id_t       lc_ctrl_otp_device_id;
  otp_ctrl_pkg::otp_device_id_t       keymgr_otp_device_id;
  otp_ctrl_pkg::otp_en_t       sram_ctrl_main_otp_en_sram_ifetch;
  otp_ctrl_pkg::otp_en_t       sram_ctrl_ret_aon_otp_en_sram_ifetch;

  // define mixed connection to port
  assign edn0_edn_req[2] = ast_edn_req_i;
  assign ast_edn_rsp_o = edn0_edn_rsp[2];
  assign ast_lc_dft_en_o = lc_ctrl_lc_dft_en;
  assign ast_ram_1p_cfg = ram_1p_cfg_i;
  assign ast_ram_2p_cfg = ram_2p_cfg_i;
  assign ast_rom_cfg = rom_cfg_i;

  // define partial inter-module tie-off
  edn_pkg::edn_rsp_t unused_edn1_edn_rsp1;
  edn_pkg::edn_rsp_t unused_edn1_edn_rsp2;
  edn_pkg::edn_rsp_t unused_edn1_edn_rsp3;
  edn_pkg::edn_rsp_t unused_edn1_edn_rsp4;
  edn_pkg::edn_rsp_t unused_edn1_edn_rsp5;
  edn_pkg::edn_rsp_t unused_edn1_edn_rsp6;

  // assign partial inter-module tie-off
  assign unused_edn1_edn_rsp1 = edn1_edn_rsp[1];
  assign unused_edn1_edn_rsp2 = edn1_edn_rsp[2];
  assign unused_edn1_edn_rsp3 = edn1_edn_rsp[3];
  assign unused_edn1_edn_rsp4 = edn1_edn_rsp[4];
  assign unused_edn1_edn_rsp5 = edn1_edn_rsp[5];
  assign unused_edn1_edn_rsp6 = edn1_edn_rsp[6];
  assign edn1_edn_req[1] = '0;
  assign edn1_edn_req[2] = '0;
  assign edn1_edn_req[3] = '0;
  assign edn1_edn_req[4] = '0;
  assign edn1_edn_req[5] = '0;
  assign edn1_edn_req[6] = '0;


  // OTP HW_CFG Broadcast signals.
  // TODO(#6713): The actual struct breakout and mapping currently needs to
  // be performed by hand.
  assign csrng_otp_en_csrng_sw_app_read = otp_ctrl_otp_hw_cfg.data.en_csrng_sw_app_read;
  assign entropy_src_otp_en_entropy_src_fw_read = otp_ctrl_otp_hw_cfg.data.en_entropy_src_fw_read;
  assign entropy_src_otp_en_entropy_src_fw_over = otp_ctrl_otp_hw_cfg.data.en_entropy_src_fw_over;
  assign sram_ctrl_main_otp_en_sram_ifetch = otp_ctrl_otp_hw_cfg.data.en_sram_ifetch;
  assign sram_ctrl_ret_aon_otp_en_sram_ifetch = otp_ctrl_otp_hw_cfg.data.en_sram_ifetch;
  assign lc_ctrl_otp_device_id = otp_ctrl_otp_hw_cfg.data.device_id;
  assign keymgr_otp_device_id = otp_ctrl_otp_hw_cfg.data.device_id;

  logic unused_otp_hw_cfg_bits;
  assign unused_otp_hw_cfg_bits = ^{
    otp_ctrl_otp_hw_cfg.valid,
    otp_ctrl_otp_hw_cfg.data.hw_cfg_digest,
    otp_ctrl_otp_hw_cfg.data.unallocated
  };

  // Unused reset signals
  logic unused_d0_rst_por_aon;
  logic unused_d0_rst_por;
  logic unused_d0_rst_por_io;
  logic unused_d0_rst_por_io_div2;
  logic unused_d0_rst_por_io_div4;
  logic unused_d0_rst_por_usb;
  logic unused_daon_rst_lc;
  logic unused_daon_rst_sys;
  logic unused_daon_rst_spi_device;
  logic unused_daon_rst_spi_host0;
  logic unused_daon_rst_spi_host1;
  logic unused_daon_rst_usb;
  logic unused_daon_rst_i2c0;
  logic unused_daon_rst_i2c1;
  logic unused_daon_rst_i2c2;
  assign unused_d0_rst_por_aon = rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por = rstmgr_aon_resets.rst_por_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_io = rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_io_div2 = rstmgr_aon_resets.rst_por_io_div2_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_io_div4 = rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_usb = rstmgr_aon_resets.rst_por_usb_n[rstmgr_pkg::Domain0Sel];
  assign unused_daon_rst_lc = rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_sys = rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_spi_device = rstmgr_aon_resets.rst_spi_device_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_spi_host0 = rstmgr_aon_resets.rst_spi_host0_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_spi_host1 = rstmgr_aon_resets.rst_spi_host1_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_usb = rstmgr_aon_resets.rst_usb_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_i2c0 = rstmgr_aon_resets.rst_i2c0_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_i2c1 = rstmgr_aon_resets.rst_i2c1_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_i2c2 = rstmgr_aon_resets.rst_i2c2_n[rstmgr_pkg::DomainAonSel];

  // processor core
  rv_core_ibex #(
    .PMPEnable                (1),
    .PMPGranularity           (0), // 2^(PMPGranularity+2) == 4 byte granularity
    .PMPNumRegions            (16),
    .MHPMCounterNum           (10),
    .MHPMCounterWidth         (32),
    .RV32E                    (0),
    .RV32M                    (ibex_pkg::RV32MSingleCycle),
    .RV32B                    (ibex_pkg::RV32BNone),
    .RegFile                  (IbexRegFile),
    .BranchTargetALU          (1),
    .WritebackStage           (1),
    .ICache                   (IbexICache),
    .ICacheECC                (1),
    .BranchPredictor          (0),
    .DbgTriggerEn             (1),
    .SecureIbex               (SecureIbex),
    .DmHaltAddr               (ADDR_SPACE_RV_DM__ROM + dm::HaltAddress[31:0]),
    .DmExceptionAddr          (ADDR_SPACE_RV_DM__ROM + dm::ExceptionAddress[31:0]),
    .PipeLine                 (IbexPipeLine)
  ) u_rv_core_ibex (
    // clock and reset
    .clk_i                (clkmgr_aon_clocks.clk_proc_main),
    .rst_ni               (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .clk_esc_i            (clkmgr_aon_clocks.clk_io_div4_timers),
    .rst_esc_ni           (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),
    // reset feedback to the clock manager
    .rst_cpu_n_o          (rstmgr_aon_rst_cpu_n),
    .ram_cfg_i            (ast_ram_1p_cfg),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_ROM_CTRL__ROM),
    // TL-UL buses
    .tl_i_o               (main_tl_corei_req),
    .tl_i_i               (main_tl_corei_rsp),
    .tl_d_o               (main_tl_cored_req),
    .tl_d_i               (main_tl_cored_rsp),
    // interrupts
    .irq_software_i       (msip),
    .irq_timer_i          (intr_rv_timer_timer_expired_0_0),
    .irq_external_i       (irq_plic),
    // escalation input from alert handler (NMI)
    .esc_tx_i             (alert_handler_esc_tx[0]),
    .esc_rx_o             (alert_handler_esc_rx[0]),
    // debug interface
    .debug_req_i          (rv_dm_debug_req),
    // crash dump interface
    .crash_dump_o         (rv_core_ibex_crash_dump),
    // CPU control signals
    .lc_cpu_en_i          (lc_ctrl_lc_cpu_en),
    .pwrmgr_cpu_en_i      (pwrmgr_aon_fetch_en),
    .core_sleep_o         (pwrmgr_aon_pwr_cpu.core_sleeping),
    // alert hooksup
    .fatal_intg_event_o   (rv_core_ibex_fatal_intg_event),
    .fatal_core_event_o   (rv_core_ibex_fatal_core_event),
    .recov_core_event_o   (rv_core_ibex_recov_core_event),
    // address translation configuration
    .ibus_region_cfg_i    (rv_core_ibex_peri_ibus_region_cfg),
    .dbus_region_cfg_i    (rv_core_ibex_peri_dbus_region_cfg),
    // dft bypass
    .scan_rst_ni,
    .scanmode_i
  );

  // Struct breakout module tool-inserted DFT TAP signals
  pinmux_jtag_breakout u_dft_tap_breakout (
    .req_i    (pinmux_aon_dft_jtag_req),
    .rsp_o    (pinmux_aon_dft_jtag_rsp),
    .tck_o    (),
    .trst_no  (),
    .tms_o    (),
    .tdi_o    (),
    .tdo_i    (1'b0),
    .tdo_oe_i (1'b0)
  );


  // host to flash communication
  logic flash_host_req;
  tlul_pkg::tl_type_e flash_host_req_type;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic flash_host_rderr;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;
  logic flash_host_intg_err;

  tlul_adapter_sram #(
    .SramAw(flash_ctrl_pkg::BusAddrW),
    .SramDw(flash_ctrl_pkg::BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_tl_adapter_eflash (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),

    .tl_i        (eflash_tl_req),
    .tl_o        (eflash_tl_rsp),
    .en_ifetch_i (tlul_pkg::InstrEn), // tie this to secure boot somehow
    .req_o       (flash_host_req),
    .req_type_o  (flash_host_req_type),
    .gnt_i       (flash_host_req_rdy),
    .we_o        (),
    .addr_o      (flash_host_addr),
    .wdata_o     (),
    .wmask_o     (),
    .intg_error_o(flash_host_intg_err),
    .rdata_i     (flash_host_rdata),
    .rvalid_i    (flash_host_req_done),
    .rerror_i    ({flash_host_rderr,1'b0})
  );

  flash_phy u_flash_eflash (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .host_req_i        (flash_host_req),
    .host_intg_err_i   (flash_host_intg_err),
    .host_req_type_i   (flash_host_req_type),
    .host_addr_i       (flash_host_addr),
    .host_req_rdy_o    (flash_host_req_rdy),
    .host_req_done_o   (flash_host_req_done),
    .host_rderr_o      (flash_host_rderr),
    .host_rdata_o      (flash_host_rdata),
    .flash_ctrl_i      (flash_ctrl_flash_req),
    .flash_ctrl_o      (flash_ctrl_flash_rsp),
    .lc_nvm_debug_en_i (lc_ctrl_lc_nvm_debug_en),
    .flash_bist_enable_i,
    .flash_power_down_h_i,
    .flash_power_ready_h_i,
    .flash_test_mode_a_io,
    .flash_test_voltage_h_io,
    .flash_alert_o,
    .scanmode_i,
    .scan_en_i,
    .scan_rst_ni
  );



  uart #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[0:0])
  ) u_uart0 (

      // Input
      .cio_rx_i    (cio_uart0_rx_p2d),

      // Output
      .cio_tx_o    (cio_uart0_tx_d2p),
      .cio_tx_en_o (cio_uart0_tx_en_d2p),

      // Interrupt
      .intr_tx_watermark_o  (intr_uart0_tx_watermark),
      .intr_rx_watermark_o  (intr_uart0_rx_watermark),
      .intr_tx_empty_o      (intr_uart0_tx_empty),
      .intr_rx_overflow_o   (intr_uart0_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart0_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart0_rx_break_err),
      .intr_rx_timeout_o    (intr_uart0_rx_timeout),
      .intr_rx_parity_err_o (intr_uart0_rx_parity_err),
      // [0]: fatal_fault
      .alert_tx_o  ( alert_tx[0:0] ),
      .alert_rx_i  ( alert_rx[0:0] ),

      // Inter-module signals
      .tl_i(uart0_tl_req),
      .tl_o(uart0_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  uart #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[1:1])
  ) u_uart1 (

      // Input
      .cio_rx_i    (cio_uart1_rx_p2d),

      // Output
      .cio_tx_o    (cio_uart1_tx_d2p),
      .cio_tx_en_o (cio_uart1_tx_en_d2p),

      // Interrupt
      .intr_tx_watermark_o  (intr_uart1_tx_watermark),
      .intr_rx_watermark_o  (intr_uart1_rx_watermark),
      .intr_tx_empty_o      (intr_uart1_tx_empty),
      .intr_rx_overflow_o   (intr_uart1_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart1_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart1_rx_break_err),
      .intr_rx_timeout_o    (intr_uart1_rx_timeout),
      .intr_rx_parity_err_o (intr_uart1_rx_parity_err),
      // [1]: fatal_fault
      .alert_tx_o  ( alert_tx[1:1] ),
      .alert_rx_i  ( alert_rx[1:1] ),

      // Inter-module signals
      .tl_i(uart1_tl_req),
      .tl_o(uart1_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  uart #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[2:2])
  ) u_uart2 (

      // Input
      .cio_rx_i    (cio_uart2_rx_p2d),

      // Output
      .cio_tx_o    (cio_uart2_tx_d2p),
      .cio_tx_en_o (cio_uart2_tx_en_d2p),

      // Interrupt
      .intr_tx_watermark_o  (intr_uart2_tx_watermark),
      .intr_rx_watermark_o  (intr_uart2_rx_watermark),
      .intr_tx_empty_o      (intr_uart2_tx_empty),
      .intr_rx_overflow_o   (intr_uart2_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart2_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart2_rx_break_err),
      .intr_rx_timeout_o    (intr_uart2_rx_timeout),
      .intr_rx_parity_err_o (intr_uart2_rx_parity_err),
      // [2]: fatal_fault
      .alert_tx_o  ( alert_tx[2:2] ),
      .alert_rx_i  ( alert_rx[2:2] ),

      // Inter-module signals
      .tl_i(uart2_tl_req),
      .tl_o(uart2_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  uart #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[3:3])
  ) u_uart3 (

      // Input
      .cio_rx_i    (cio_uart3_rx_p2d),

      // Output
      .cio_tx_o    (cio_uart3_tx_d2p),
      .cio_tx_en_o (cio_uart3_tx_en_d2p),

      // Interrupt
      .intr_tx_watermark_o  (intr_uart3_tx_watermark),
      .intr_rx_watermark_o  (intr_uart3_rx_watermark),
      .intr_tx_empty_o      (intr_uart3_tx_empty),
      .intr_rx_overflow_o   (intr_uart3_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart3_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart3_rx_break_err),
      .intr_rx_timeout_o    (intr_uart3_rx_timeout),
      .intr_rx_parity_err_o (intr_uart3_rx_parity_err),
      // [3]: fatal_fault
      .alert_tx_o  ( alert_tx[3:3] ),
      .alert_rx_i  ( alert_rx[3:3] ),

      // Inter-module signals
      .tl_i(uart3_tl_req),
      .tl_o(uart3_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  gpio #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[4:4])
  ) u_gpio (

      // Input
      .cio_gpio_i    (cio_gpio_gpio_p2d),

      // Output
      .cio_gpio_o    (cio_gpio_gpio_d2p),
      .cio_gpio_en_o (cio_gpio_gpio_en_d2p),

      // Interrupt
      .intr_gpio_o (intr_gpio_gpio),
      // [4]: fatal_fault
      .alert_tx_o  ( alert_tx[4:4] ),
      .alert_rx_i  ( alert_rx[4:4] ),

      // Inter-module signals
      .tl_i(gpio_tl_req),
      .tl_o(gpio_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  spi_device #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[5:5])
  ) u_spi_device (

      // Input
      .cio_sck_i    (cio_spi_device_sck_p2d),
      .cio_csb_i    (cio_spi_device_csb_p2d),
      .cio_sd_i     (cio_spi_device_sd_p2d),

      // Output
      .cio_sd_o     (cio_spi_device_sd_d2p),
      .cio_sd_en_o  (cio_spi_device_sd_en_d2p),

      // Interrupt
      .intr_rxf_o         (intr_spi_device_rxf),
      .intr_rxlvl_o       (intr_spi_device_rxlvl),
      .intr_txlvl_o       (intr_spi_device_txlvl),
      .intr_rxerr_o       (intr_spi_device_rxerr),
      .intr_rxoverflow_o  (intr_spi_device_rxoverflow),
      .intr_txunderflow_o (intr_spi_device_txunderflow),
      // [5]: fatal_fault
      .alert_tx_o  ( alert_tx[5:5] ),
      .alert_rx_i  ( alert_rx[5:5] ),

      // Inter-module signals
      .ram_cfg_i(ast_ram_2p_cfg),
      .passthrough_o(spi_device_passthrough_req),
      .passthrough_i(spi_device_passthrough_rsp),
      .mbist_en_i('0),
      .tl_i(spi_device_tl_req),
      .tl_o(spi_device_tl_rsp),
      .scanmode_i,
      .scan_rst_ni,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .scan_clk_i (clkmgr_aon_clocks.clk_io_div2_peri),
      .rst_ni (rstmgr_aon_resets.rst_spi_device_n[rstmgr_pkg::Domain0Sel])
  );

  spi_host #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[6:6])
  ) u_spi_host0 (

      // Input
      .cio_sd_i     (cio_spi_host0_sd_p2d),

      // Output
      .cio_sck_o    (cio_spi_host0_sck_d2p),
      .cio_sck_en_o (cio_spi_host0_sck_en_d2p),
      .cio_csb_o    (cio_spi_host0_csb_d2p),
      .cio_csb_en_o (cio_spi_host0_csb_en_d2p),
      .cio_sd_o     (cio_spi_host0_sd_d2p),
      .cio_sd_en_o  (cio_spi_host0_sd_en_d2p),

      // Interrupt
      .intr_error_o     (intr_spi_host0_error),
      .intr_spi_event_o (intr_spi_host0_spi_event),
      // [6]: fatal_fault
      .alert_tx_o  ( alert_tx[6:6] ),
      .alert_rx_i  ( alert_rx[6:6] ),

      // Inter-module signals
      .passthrough_i(spi_device_passthrough_req),
      .passthrough_o(spi_device_passthrough_rsp),
      .tl_i(spi_host0_tl_req),
      .tl_o(spi_host0_tl_rsp),
      .scanmode_i,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .clk_core_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_spi_host0_n[rstmgr_pkg::Domain0Sel]),
      .rst_core_ni (rstmgr_aon_resets.rst_spi_host0_n[rstmgr_pkg::Domain0Sel])
  );

  spi_host #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[7:7])
  ) u_spi_host1 (

      // Input
      .cio_sd_i     (cio_spi_host1_sd_p2d),

      // Output
      .cio_sck_o    (cio_spi_host1_sck_d2p),
      .cio_sck_en_o (cio_spi_host1_sck_en_d2p),
      .cio_csb_o    (cio_spi_host1_csb_d2p),
      .cio_csb_en_o (cio_spi_host1_csb_en_d2p),
      .cio_sd_o     (cio_spi_host1_sd_d2p),
      .cio_sd_en_o  (cio_spi_host1_sd_en_d2p),

      // Interrupt
      .intr_error_o     (intr_spi_host1_error),
      .intr_spi_event_o (intr_spi_host1_spi_event),
      // [7]: fatal_fault
      .alert_tx_o  ( alert_tx[7:7] ),
      .alert_rx_i  ( alert_rx[7:7] ),

      // Inter-module signals
      .passthrough_i(spi_device_pkg::PASSTHROUGH_REQ_DEFAULT),
      .passthrough_o(),
      .tl_i(spi_host1_tl_req),
      .tl_o(spi_host1_tl_rsp),
      .scanmode_i,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .clk_core_i (clkmgr_aon_clocks.clk_io_div2_peri),
      .rst_ni (rstmgr_aon_resets.rst_spi_host1_n[rstmgr_pkg::Domain0Sel]),
      .rst_core_ni (rstmgr_aon_resets.rst_spi_host1_n[rstmgr_pkg::Domain0Sel])
  );

  i2c #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[8:8])
  ) u_i2c0 (

      // Input
      .cio_sda_i    (cio_i2c0_sda_p2d),
      .cio_scl_i    (cio_i2c0_scl_p2d),

      // Output
      .cio_sda_o    (cio_i2c0_sda_d2p),
      .cio_sda_en_o (cio_i2c0_sda_en_d2p),
      .cio_scl_o    (cio_i2c0_scl_d2p),
      .cio_scl_en_o (cio_i2c0_scl_en_d2p),

      // Interrupt
      .intr_fmt_watermark_o    (intr_i2c0_fmt_watermark),
      .intr_rx_watermark_o     (intr_i2c0_rx_watermark),
      .intr_fmt_overflow_o     (intr_i2c0_fmt_overflow),
      .intr_rx_overflow_o      (intr_i2c0_rx_overflow),
      .intr_nak_o              (intr_i2c0_nak),
      .intr_scl_interference_o (intr_i2c0_scl_interference),
      .intr_sda_interference_o (intr_i2c0_sda_interference),
      .intr_stretch_timeout_o  (intr_i2c0_stretch_timeout),
      .intr_sda_unstable_o     (intr_i2c0_sda_unstable),
      .intr_trans_complete_o   (intr_i2c0_trans_complete),
      .intr_tx_empty_o         (intr_i2c0_tx_empty),
      .intr_tx_nonempty_o      (intr_i2c0_tx_nonempty),
      .intr_tx_overflow_o      (intr_i2c0_tx_overflow),
      .intr_acq_overflow_o     (intr_i2c0_acq_overflow),
      .intr_ack_stop_o         (intr_i2c0_ack_stop),
      .intr_host_timeout_o     (intr_i2c0_host_timeout),
      // [8]: fatal_fault
      .alert_tx_o  ( alert_tx[8:8] ),
      .alert_rx_i  ( alert_rx[8:8] ),

      // Inter-module signals
      .tl_i(i2c0_tl_req),
      .tl_o(i2c0_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_aon_resets.rst_i2c0_n[rstmgr_pkg::Domain0Sel])
  );

  i2c #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[9:9])
  ) u_i2c1 (

      // Input
      .cio_sda_i    (cio_i2c1_sda_p2d),
      .cio_scl_i    (cio_i2c1_scl_p2d),

      // Output
      .cio_sda_o    (cio_i2c1_sda_d2p),
      .cio_sda_en_o (cio_i2c1_sda_en_d2p),
      .cio_scl_o    (cio_i2c1_scl_d2p),
      .cio_scl_en_o (cio_i2c1_scl_en_d2p),

      // Interrupt
      .intr_fmt_watermark_o    (intr_i2c1_fmt_watermark),
      .intr_rx_watermark_o     (intr_i2c1_rx_watermark),
      .intr_fmt_overflow_o     (intr_i2c1_fmt_overflow),
      .intr_rx_overflow_o      (intr_i2c1_rx_overflow),
      .intr_nak_o              (intr_i2c1_nak),
      .intr_scl_interference_o (intr_i2c1_scl_interference),
      .intr_sda_interference_o (intr_i2c1_sda_interference),
      .intr_stretch_timeout_o  (intr_i2c1_stretch_timeout),
      .intr_sda_unstable_o     (intr_i2c1_sda_unstable),
      .intr_trans_complete_o   (intr_i2c1_trans_complete),
      .intr_tx_empty_o         (intr_i2c1_tx_empty),
      .intr_tx_nonempty_o      (intr_i2c1_tx_nonempty),
      .intr_tx_overflow_o      (intr_i2c1_tx_overflow),
      .intr_acq_overflow_o     (intr_i2c1_acq_overflow),
      .intr_ack_stop_o         (intr_i2c1_ack_stop),
      .intr_host_timeout_o     (intr_i2c1_host_timeout),
      // [9]: fatal_fault
      .alert_tx_o  ( alert_tx[9:9] ),
      .alert_rx_i  ( alert_rx[9:9] ),

      // Inter-module signals
      .tl_i(i2c1_tl_req),
      .tl_o(i2c1_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_aon_resets.rst_i2c1_n[rstmgr_pkg::Domain0Sel])
  );

  i2c #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[10:10])
  ) u_i2c2 (

      // Input
      .cio_sda_i    (cio_i2c2_sda_p2d),
      .cio_scl_i    (cio_i2c2_scl_p2d),

      // Output
      .cio_sda_o    (cio_i2c2_sda_d2p),
      .cio_sda_en_o (cio_i2c2_sda_en_d2p),
      .cio_scl_o    (cio_i2c2_scl_d2p),
      .cio_scl_en_o (cio_i2c2_scl_en_d2p),

      // Interrupt
      .intr_fmt_watermark_o    (intr_i2c2_fmt_watermark),
      .intr_rx_watermark_o     (intr_i2c2_rx_watermark),
      .intr_fmt_overflow_o     (intr_i2c2_fmt_overflow),
      .intr_rx_overflow_o      (intr_i2c2_rx_overflow),
      .intr_nak_o              (intr_i2c2_nak),
      .intr_scl_interference_o (intr_i2c2_scl_interference),
      .intr_sda_interference_o (intr_i2c2_sda_interference),
      .intr_stretch_timeout_o  (intr_i2c2_stretch_timeout),
      .intr_sda_unstable_o     (intr_i2c2_sda_unstable),
      .intr_trans_complete_o   (intr_i2c2_trans_complete),
      .intr_tx_empty_o         (intr_i2c2_tx_empty),
      .intr_tx_nonempty_o      (intr_i2c2_tx_nonempty),
      .intr_tx_overflow_o      (intr_i2c2_tx_overflow),
      .intr_acq_overflow_o     (intr_i2c2_acq_overflow),
      .intr_ack_stop_o         (intr_i2c2_ack_stop),
      .intr_host_timeout_o     (intr_i2c2_host_timeout),
      // [10]: fatal_fault
      .alert_tx_o  ( alert_tx[10:10] ),
      .alert_rx_i  ( alert_rx[10:10] ),

      // Inter-module signals
      .tl_i(i2c2_tl_req),
      .tl_o(i2c2_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_aon_resets.rst_i2c2_n[rstmgr_pkg::Domain0Sel])
  );

  pattgen #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[11:11])
  ) u_pattgen (

      // Output
      .cio_pda0_tx_o    (cio_pattgen_pda0_tx_d2p),
      .cio_pda0_tx_en_o (cio_pattgen_pda0_tx_en_d2p),
      .cio_pcl0_tx_o    (cio_pattgen_pcl0_tx_d2p),
      .cio_pcl0_tx_en_o (cio_pattgen_pcl0_tx_en_d2p),
      .cio_pda1_tx_o    (cio_pattgen_pda1_tx_d2p),
      .cio_pda1_tx_en_o (cio_pattgen_pda1_tx_en_d2p),
      .cio_pcl1_tx_o    (cio_pattgen_pcl1_tx_d2p),
      .cio_pcl1_tx_en_o (cio_pattgen_pcl1_tx_en_d2p),

      // Interrupt
      .intr_done_ch0_o (intr_pattgen_done_ch0),
      .intr_done_ch1_o (intr_pattgen_done_ch1),
      // [11]: fatal_fault
      .alert_tx_o  ( alert_tx[11:11] ),
      .alert_rx_i  ( alert_rx[11:11] ),

      // Inter-module signals
      .tl_i(pattgen_tl_req),
      .tl_o(pattgen_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  rv_timer #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[12:12])
  ) u_rv_timer (

      // Interrupt
      .intr_timer_expired_0_0_o (intr_rv_timer_timer_expired_0_0),
      // [12]: fatal_fault
      .alert_tx_o  ( alert_tx[12:12] ),
      .alert_rx_i  ( alert_rx[12:12] ),

      // Inter-module signals
      .tl_i(rv_timer_tl_req),
      .tl_o(rv_timer_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_timers),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  usbdev #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[13:13])
  ) u_usbdev (

      // Input
      .cio_sense_i         (cio_usbdev_sense_p2d),
      .cio_d_i             (cio_usbdev_d_p2d),
      .cio_dp_i            (cio_usbdev_dp_p2d),
      .cio_dn_i            (cio_usbdev_dn_p2d),

      // Output
      .cio_se0_o           (cio_usbdev_se0_d2p),
      .cio_se0_en_o        (cio_usbdev_se0_en_d2p),
      .cio_dp_pullup_o     (cio_usbdev_dp_pullup_d2p),
      .cio_dp_pullup_en_o  (cio_usbdev_dp_pullup_en_d2p),
      .cio_dn_pullup_o     (cio_usbdev_dn_pullup_d2p),
      .cio_dn_pullup_en_o  (cio_usbdev_dn_pullup_en_d2p),
      .cio_tx_mode_se_o    (cio_usbdev_tx_mode_se_d2p),
      .cio_tx_mode_se_en_o (cio_usbdev_tx_mode_se_en_d2p),
      .cio_suspend_o       (cio_usbdev_suspend_d2p),
      .cio_suspend_en_o    (cio_usbdev_suspend_en_d2p),
      .cio_rx_enable_o     (cio_usbdev_rx_enable_d2p),
      .cio_rx_enable_en_o  (cio_usbdev_rx_enable_en_d2p),
      .cio_d_o             (cio_usbdev_d_d2p),
      .cio_d_en_o          (cio_usbdev_d_en_d2p),
      .cio_dp_o            (cio_usbdev_dp_d2p),
      .cio_dp_en_o         (cio_usbdev_dp_en_d2p),
      .cio_dn_o            (cio_usbdev_dn_d2p),
      .cio_dn_en_o         (cio_usbdev_dn_en_d2p),

      // Interrupt
      .intr_pkt_received_o    (intr_usbdev_pkt_received),
      .intr_pkt_sent_o        (intr_usbdev_pkt_sent),
      .intr_disconnected_o    (intr_usbdev_disconnected),
      .intr_host_lost_o       (intr_usbdev_host_lost),
      .intr_link_reset_o      (intr_usbdev_link_reset),
      .intr_link_suspend_o    (intr_usbdev_link_suspend),
      .intr_link_resume_o     (intr_usbdev_link_resume),
      .intr_av_empty_o        (intr_usbdev_av_empty),
      .intr_rx_full_o         (intr_usbdev_rx_full),
      .intr_av_overflow_o     (intr_usbdev_av_overflow),
      .intr_link_in_err_o     (intr_usbdev_link_in_err),
      .intr_rx_crc_err_o      (intr_usbdev_rx_crc_err),
      .intr_rx_pid_err_o      (intr_usbdev_rx_pid_err),
      .intr_rx_bitstuff_err_o (intr_usbdev_rx_bitstuff_err),
      .intr_frame_o           (intr_usbdev_frame),
      .intr_connected_o       (intr_usbdev_connected),
      .intr_link_out_err_o    (intr_usbdev_link_out_err),
      // [13]: fatal_fault
      .alert_tx_o  ( alert_tx[13:13] ),
      .alert_rx_i  ( alert_rx[13:13] ),

      // Inter-module signals
      .usb_ref_val_o(usbdev_usb_ref_val_o),
      .usb_ref_pulse_o(usbdev_usb_ref_pulse_o),
      .usb_out_of_rst_o(usbdev_usb_out_of_rst),
      .usb_aon_wake_en_o(usbdev_usb_aon_wake_en),
      .usb_aon_wake_ack_o(usbdev_usb_aon_wake_ack),
      .usb_suspend_o(usbdev_usb_suspend),
      .usb_state_debug_i(pinmux_aon_usb_state_debug),
      .ram_cfg_i(ast_ram_2p_cfg),
      .tl_i(usbdev_tl_req),
      .tl_o(usbdev_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_peri),
      .clk_usb_48mhz_i (clkmgr_aon_clocks.clk_usb_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),
      .rst_aon_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::Domain0Sel]),
      .rst_usb_48mhz_ni (rstmgr_aon_resets.rst_usb_n[rstmgr_pkg::Domain0Sel])
  );

  otp_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[16:14]),
    .MemInitFile(OtpCtrlMemInitFile),
    .RndCnstLfsrSeed(RndCnstOtpCtrlLfsrSeed),
    .RndCnstLfsrPerm(RndCnstOtpCtrlLfsrPerm)
  ) u_otp_ctrl (

      // Interrupt
      .intr_otp_operation_done_o (intr_otp_ctrl_otp_operation_done),
      .intr_otp_error_o          (intr_otp_ctrl_otp_error),
      // [14]: fatal_macro_error
      // [15]: fatal_check_error
      // [16]: fatal_bus_integ_error
      .alert_tx_o  ( alert_tx[16:14] ),
      .alert_rx_i  ( alert_rx[16:14] ),

      // Inter-module signals
      .otp_ast_pwr_seq_o(otp_ctrl_otp_ast_pwr_seq_o),
      .otp_ast_pwr_seq_h_i(otp_ctrl_otp_ast_pwr_seq_h_i),
      .otp_alert_o(otp_alert_o),
      .edn_o(edn0_edn_req[1]),
      .edn_i(edn0_edn_rsp[1]),
      .pwr_otp_i(pwrmgr_aon_pwr_otp_req),
      .pwr_otp_o(pwrmgr_aon_pwr_otp_rsp),
      .lc_otp_program_i(lc_ctrl_lc_otp_program_req),
      .lc_otp_program_o(lc_ctrl_lc_otp_program_rsp),
      .otp_lc_data_o(otp_ctrl_otp_lc_data),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .lc_creator_seed_sw_rw_en_i(lc_ctrl_lc_creator_seed_sw_rw_en),
      .lc_seed_hw_rd_en_i(lc_ctrl_lc_seed_hw_rd_en),
      .lc_dft_en_i(lc_ctrl_lc_dft_en),
      .lc_check_byp_en_i(lc_ctrl_lc_check_byp_en),
      .otp_keymgr_key_o(otp_ctrl_otp_keymgr_key),
      .flash_otp_key_i(flash_ctrl_otp_req),
      .flash_otp_key_o(flash_ctrl_otp_rsp),
      .sram_otp_key_i(otp_ctrl_sram_otp_key_req),
      .sram_otp_key_o(otp_ctrl_sram_otp_key_rsp),
      .otbn_otp_key_i(otp_ctrl_otbn_otp_key_req),
      .otbn_otp_key_o(otp_ctrl_otbn_otp_key_rsp),
      .otp_hw_cfg_o(otp_ctrl_otp_hw_cfg),
      .tl_i(otp_ctrl_tl_req),
      .tl_o(otp_ctrl_tl_rsp),
      .otp_ext_voltage_h_io,
      .scanmode_i,
      .scan_rst_ni,
      .scan_en_i,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_timers),
      .clk_edn_i (clkmgr_aon_clocks.clk_main_timers),
      .rst_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  lc_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[19:17]),
    .RndCnstLcKeymgrDivInvalid(RndCnstLcCtrlLcKeymgrDivInvalid),
    .RndCnstLcKeymgrDivTestDevRma(RndCnstLcCtrlLcKeymgrDivTestDevRma),
    .RndCnstLcKeymgrDivProduction(RndCnstLcCtrlLcKeymgrDivProduction)
  ) u_lc_ctrl (
      // [17]: fatal_prog_error
      // [18]: fatal_state_error
      // [19]: fatal_bus_integ_error
      .alert_tx_o  ( alert_tx[19:17] ),
      .alert_rx_i  ( alert_rx[19:17] ),

      // Inter-module signals
      .jtag_i(pinmux_aon_lc_jtag_req),
      .jtag_o(pinmux_aon_lc_jtag_rsp),
      .esc_scrap_state0_tx_i(alert_handler_esc_tx[1]),
      .esc_scrap_state0_rx_o(alert_handler_esc_rx[1]),
      .esc_scrap_state1_tx_i(alert_handler_esc_tx[2]),
      .esc_scrap_state1_rx_o(alert_handler_esc_rx[2]),
      .pwr_lc_i(pwrmgr_aon_pwr_lc_req),
      .pwr_lc_o(pwrmgr_aon_pwr_lc_rsp),
      .otp_lc_data_i(otp_ctrl_otp_lc_data),
      .lc_otp_program_o(lc_ctrl_lc_otp_program_req),
      .lc_otp_program_i(lc_ctrl_lc_otp_program_rsp),
      .kmac_data_o(kmac_app_req[1]),
      .kmac_data_i(kmac_app_rsp[1]),
      .lc_dft_en_o(lc_ctrl_lc_dft_en),
      .lc_nvm_debug_en_o(lc_ctrl_lc_nvm_debug_en),
      .lc_hw_debug_en_o(lc_ctrl_lc_hw_debug_en),
      .lc_cpu_en_o(lc_ctrl_lc_cpu_en),
      .lc_keymgr_en_o(lc_ctrl_lc_keymgr_en),
      .lc_escalate_en_o(lc_ctrl_lc_escalate_en),
      .lc_clk_byp_req_o(lc_ctrl_lc_clk_byp_req),
      .lc_clk_byp_ack_i(lc_ctrl_lc_clk_byp_ack),
      .lc_flash_rma_req_o(flash_ctrl_rma_req),
      .lc_flash_rma_seed_o(flash_ctrl_rma_seed),
      .lc_flash_rma_ack_i(flash_ctrl_rma_ack),
      .lc_check_byp_en_o(lc_ctrl_lc_check_byp_en),
      .lc_creator_seed_sw_rw_en_o(lc_ctrl_lc_creator_seed_sw_rw_en),
      .lc_owner_seed_sw_rw_en_o(lc_ctrl_lc_owner_seed_sw_rw_en),
      .lc_iso_part_sw_rd_en_o(lc_ctrl_lc_iso_part_sw_rd_en),
      .lc_iso_part_sw_wr_en_o(lc_ctrl_lc_iso_part_sw_wr_en),
      .lc_seed_hw_rd_en_o(lc_ctrl_lc_seed_hw_rd_en),
      .lc_keymgr_div_o(lc_ctrl_lc_keymgr_div),
      .otp_device_id_i(lc_ctrl_otp_device_id),
      .tl_i(lc_ctrl_tl_req),
      .tl_o(lc_ctrl_tl_rsp),
      .scanmode_i,
      .scan_rst_ni,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_timers),
      .clk_kmac_i (clkmgr_aon_clocks.clk_main_timers),
      .rst_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
      .rst_kmac_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  alert_handler #(
    .RndCnstLfsrSeed(RndCnstAlertHandlerLfsrSeed),
    .RndCnstLfsrPerm(RndCnstAlertHandlerLfsrPerm)
  ) u_alert_handler (

      // Interrupt
      .intr_classa_o (intr_alert_handler_classa),
      .intr_classb_o (intr_alert_handler_classb),
      .intr_classc_o (intr_alert_handler_classc),
      .intr_classd_o (intr_alert_handler_classd),

      // Inter-module signals
      .crashdump_o(alert_handler_crashdump),
      .edn_o(edn0_edn_req[4]),
      .edn_i(edn0_edn_rsp[4]),
      .esc_rx_i(alert_handler_esc_rx),
      .esc_tx_o(alert_handler_esc_tx),
      .tl_i(alert_handler_tl_req),
      .tl_o(alert_handler_tl_rsp),
      // alert signals
      .alert_rx_o  ( alert_rx ),
      .alert_tx_i  ( alert_tx ),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_timers),
      .clk_edn_i (clkmgr_aon_clocks.clk_main_timers),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  pwrmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[20:20])
  ) u_pwrmgr_aon (

      // Interrupt
      .intr_wakeup_o (intr_pwrmgr_aon_wakeup),
      // [20]: fatal_fault
      .alert_tx_o  ( alert_tx[20:20] ),
      .alert_rx_i  ( alert_rx[20:20] ),

      // Inter-module signals
      .pwr_ast_o(pwrmgr_ast_req_o),
      .pwr_ast_i(pwrmgr_ast_rsp_i),
      .pwr_rst_o(pwrmgr_aon_pwr_rst_req),
      .pwr_rst_i(pwrmgr_aon_pwr_rst_rsp),
      .pwr_clk_o(pwrmgr_aon_pwr_clk_req),
      .pwr_clk_i(pwrmgr_aon_pwr_clk_rsp),
      .pwr_otp_o(pwrmgr_aon_pwr_otp_req),
      .pwr_otp_i(pwrmgr_aon_pwr_otp_rsp),
      .pwr_lc_o(pwrmgr_aon_pwr_lc_req),
      .pwr_lc_i(pwrmgr_aon_pwr_lc_rsp),
      .pwr_flash_i(pwrmgr_aon_pwr_flash),
      .esc_rst_tx_i(alert_handler_esc_tx[3]),
      .esc_rst_rx_o(alert_handler_esc_rx[3]),
      .pwr_cpu_i(pwrmgr_aon_pwr_cpu),
      .wakeups_i(pwrmgr_aon_wakeups),
      .rstreqs_i(pwrmgr_aon_rstreqs),
      .strap_o(pwrmgr_aon_strap),
      .low_power_o(pwrmgr_aon_low_power),
      .rom_ctrl_i(rom_ctrl_pwrmgr_data),
      .fetch_en_o(pwrmgr_aon_fetch_en),
      .tl_i(pwrmgr_aon_tl_req),
      .tl_o(pwrmgr_aon_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_powerup),
      .clk_slow_i (clkmgr_aon_clocks.clk_aon_powerup),
      .rst_ni (rstmgr_aon_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
      .rst_slow_ni (rstmgr_aon_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel])
  );

  rstmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[21:21])
  ) u_rstmgr_aon (
      // [21]: fatal_fault
      .alert_tx_o  ( alert_tx[21:21] ),
      .alert_rx_i  ( alert_rx[21:21] ),

      // Inter-module signals
      .pwr_i(pwrmgr_aon_pwr_rst_req),
      .pwr_o(pwrmgr_aon_pwr_rst_rsp),
      .resets_o(rstmgr_aon_resets),
      .rst_cpu_n_i(rstmgr_aon_rst_cpu_n),
      .ndmreset_req_i(rv_dm_ndmreset_req),
      .alert_dump_i(alert_handler_crashdump),
      .cpu_dump_i(rv_core_ibex_crash_dump),
      .resets_ast_o(rsts_ast_o),
      .tl_i(rstmgr_aon_tl_req),
      .tl_o(rstmgr_aon_tl_rsp),
      .scanmode_i,
      .scan_rst_ni,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_powerup),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_powerup),
      .clk_main_i (clkmgr_aon_clocks.clk_main_powerup),
      .clk_io_i (clkmgr_aon_clocks.clk_io_powerup),
      .clk_usb_i (clkmgr_aon_clocks.clk_usb_powerup),
      .clk_io_div2_i (clkmgr_aon_clocks.clk_io_div2_powerup),
      .clk_io_div4_i (clkmgr_aon_clocks.clk_io_div4_powerup),
      .rst_ni (rst_ni)
  );

  clkmgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[22:22])
  ) u_clkmgr_aon (
      // [22]: fatal_fault
      .alert_tx_o  ( alert_tx[22:22] ),
      .alert_rx_i  ( alert_rx[22:22] ),

      // Inter-module signals
      .clocks_o(clkmgr_aon_clocks),
      .lc_dft_en_i(lc_ctrl_lc_dft_en),
      .ast_clk_byp_req_o(ast_clk_byp_req_o),
      .ast_clk_byp_ack_i(ast_clk_byp_ack_i),
      .lc_clk_byp_req_i(lc_ctrl_lc_clk_byp_req),
      .lc_clk_byp_ack_o(lc_ctrl_lc_clk_byp_ack),
      .jitter_en_o(clk_main_jitter_en_o),
      .clk_main_i(clk_main_i),
      .clk_io_i(clk_io_i),
      .clk_usb_i(clk_usb_i),
      .clk_aon_i(clk_aon_i),
      .clocks_ast_o(clks_ast_o),
      .pwr_i(pwrmgr_aon_pwr_clk_req),
      .pwr_o(pwrmgr_aon_pwr_clk_rsp),
      .idle_i(clkmgr_aon_idle),
      .tl_i(clkmgr_aon_tl_req),
      .tl_o(clkmgr_aon_tl_rsp),
      .scanmode_i,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_powerup),
      .rst_ni (rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_main_ni (rstmgr_aon_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
      .rst_io_ni (rstmgr_aon_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
      .rst_usb_ni (rstmgr_aon_resets.rst_por_usb_n[rstmgr_pkg::DomainAonSel]),
      .rst_io_div2_ni (rstmgr_aon_resets.rst_por_io_div2_n[rstmgr_pkg::DomainAonSel]),
      .rst_io_div4_ni (rstmgr_aon_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel])
  );

  sysrst_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[23:23])
  ) u_sysrst_ctrl_aon (

      // Input
      .cio_ac_present_i      (cio_sysrst_ctrl_aon_ac_present_p2d),
      .cio_ec_rst_in_l_i     (cio_sysrst_ctrl_aon_ec_rst_in_l_p2d),
      .cio_key0_in_i         (cio_sysrst_ctrl_aon_key0_in_p2d),
      .cio_key1_in_i         (cio_sysrst_ctrl_aon_key1_in_p2d),
      .cio_key2_in_i         (cio_sysrst_ctrl_aon_key2_in_p2d),
      .cio_pwrb_in_i         (cio_sysrst_ctrl_aon_pwrb_in_p2d),
      .cio_lid_open_i        (cio_sysrst_ctrl_aon_lid_open_p2d),

      // Output
      .cio_bat_disable_o     (cio_sysrst_ctrl_aon_bat_disable_d2p),
      .cio_bat_disable_en_o  (cio_sysrst_ctrl_aon_bat_disable_en_d2p),
      .cio_ec_rst_out_l_o    (cio_sysrst_ctrl_aon_ec_rst_out_l_d2p),
      .cio_ec_rst_out_l_en_o (cio_sysrst_ctrl_aon_ec_rst_out_l_en_d2p),
      .cio_key0_out_o        (cio_sysrst_ctrl_aon_key0_out_d2p),
      .cio_key0_out_en_o     (cio_sysrst_ctrl_aon_key0_out_en_d2p),
      .cio_key1_out_o        (cio_sysrst_ctrl_aon_key1_out_d2p),
      .cio_key1_out_en_o     (cio_sysrst_ctrl_aon_key1_out_en_d2p),
      .cio_key2_out_o        (cio_sysrst_ctrl_aon_key2_out_d2p),
      .cio_key2_out_en_o     (cio_sysrst_ctrl_aon_key2_out_en_d2p),
      .cio_pwrb_out_o        (cio_sysrst_ctrl_aon_pwrb_out_d2p),
      .cio_pwrb_out_en_o     (cio_sysrst_ctrl_aon_pwrb_out_en_d2p),
      .cio_z3_wakeup_o       (cio_sysrst_ctrl_aon_z3_wakeup_d2p),
      .cio_z3_wakeup_en_o    (cio_sysrst_ctrl_aon_z3_wakeup_en_d2p),

      // Interrupt
      .intr_sysrst_ctrl_o (intr_sysrst_ctrl_aon_sysrst_ctrl),
      // [23]: fatal_fault
      .alert_tx_o  ( alert_tx[23:23] ),
      .alert_rx_i  ( alert_rx[23:23] ),

      // Inter-module signals
      .gsc_wk_o(pwrmgr_aon_wakeups[0]),
      .gsc_rst_o(pwrmgr_aon_rstreqs[0]),
      .tl_i(sysrst_ctrl_aon_tl_req),
      .tl_o(sysrst_ctrl_aon_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_aon_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel])
  );

  adc_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[24:24])
  ) u_adc_ctrl_aon (

      // Interrupt
      .intr_debug_cable_o (intr_adc_ctrl_aon_debug_cable),
      // [24]: fatal_fault
      .alert_tx_o  ( alert_tx[24:24] ),
      .alert_rx_i  ( alert_rx[24:24] ),

      // Inter-module signals
      .adc_o(adc_req_o),
      .adc_i(adc_rsp_i),
      .debug_cable_wakeup_o(pwrmgr_aon_wakeups[1]),
      .tl_i(adc_ctrl_aon_tl_req),
      .tl_o(adc_ctrl_aon_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_peri),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_slow_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel])
  );

  pwm #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[25:25])
  ) u_pwm_aon (

      // Output
      .cio_pwm_o    (cio_pwm_aon_pwm_d2p),
      .cio_pwm_en_o (cio_pwm_aon_pwm_en_d2p),
      // [25]: fatal_fault
      .alert_tx_o  ( alert_tx[25:25] ),
      .alert_rx_i  ( alert_rx[25:25] ),

      // Inter-module signals
      .tl_i(pwm_aon_tl_req),
      .tl_o(pwm_aon_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_powerup),
      .clk_core_i (clkmgr_aon_clocks.clk_aon_powerup),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_core_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel])
  );

  pinmux #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[26:26]),
    .TargetCfg(PinmuxAonTargetCfg)
  ) u_pinmux_aon (
      // [26]: fatal_fault
      .alert_tx_o  ( alert_tx[26:26] ),
      .alert_rx_i  ( alert_rx[26:26] ),

      // Inter-module signals
      .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en),
      .lc_dft_en_i(lc_ctrl_lc_dft_en),
      .lc_jtag_o(pinmux_aon_lc_jtag_req),
      .lc_jtag_i(pinmux_aon_lc_jtag_rsp),
      .rv_jtag_o(pinmux_aon_rv_jtag_req),
      .rv_jtag_i(pinmux_aon_rv_jtag_rsp),
      .dft_jtag_o(pinmux_aon_dft_jtag_req),
      .dft_jtag_i(pinmux_aon_dft_jtag_rsp),
      .dft_strap_test_o(dft_strap_test_o),
      .dft_hold_tap_sel_i(dft_hold_tap_sel_i),
      .sleep_en_i(pwrmgr_aon_low_power),
      .strap_en_i(pwrmgr_aon_strap),
      .aon_wkup_req_o(pwrmgr_aon_wakeups[2]),
      .usb_wkup_req_o(pwrmgr_aon_wakeups[3]),
      .usb_out_of_rst_i(usbdev_usb_out_of_rst),
      .usb_aon_wake_en_i(usbdev_usb_aon_wake_en),
      .usb_aon_wake_ack_i(usbdev_usb_aon_wake_ack),
      .usb_suspend_i(usbdev_usb_suspend),
      .usb_state_debug_o(pinmux_aon_usb_state_debug),
      .tl_i(pinmux_aon_tl_req),
      .tl_o(pinmux_aon_tl_rsp),

      .periph_to_mio_i      (mio_d2p    ),
      .periph_to_mio_oe_i   (mio_en_d2p ),
      .mio_to_periph_o      (mio_p2d    ),

      .mio_attr_o,
      .mio_out_o,
      .mio_oe_o,
      .mio_in_i,

      .periph_to_dio_i      (dio_d2p    ),
      .periph_to_dio_oe_i   (dio_en_d2p ),
      .dio_to_periph_o      (dio_p2d    ),

      .dio_attr_o,
      .dio_out_o,
      .dio_oe_o,
      .dio_in_i,

      .scanmode_i,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_powerup),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_powerup),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_aon_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel])
  );

  aon_timer #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[27:27])
  ) u_aon_timer_aon (

      // Interrupt
      .intr_wkup_timer_expired_o (intr_aon_timer_aon_wkup_timer_expired),
      .intr_wdog_timer_bark_o    (intr_aon_timer_aon_wdog_timer_bark),
      // [27]: fatal_fault
      .alert_tx_o  ( alert_tx[27:27] ),
      .alert_rx_i  ( alert_rx[27:27] ),

      // Inter-module signals
      .aon_timer_wkup_req_o(pwrmgr_aon_wakeups[4]),
      .aon_timer_rst_req_o(pwrmgr_aon_rstreqs[1]),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .sleep_mode_i(pwrmgr_aon_low_power),
      .tl_i(aon_timer_aon_tl_req),
      .tl_o(aon_timer_aon_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_timers),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_timers),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_aon_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel])
  );

  sensor_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[40:28])
  ) u_sensor_ctrl_aon (

      // Output
      .cio_ast_debug_out_o    (cio_sensor_ctrl_aon_ast_debug_out_d2p),
      .cio_ast_debug_out_en_o (cio_sensor_ctrl_aon_ast_debug_out_en_d2p),
      // [28]: recov_as
      // [29]: recov_cg
      // [30]: recov_gd
      // [31]: recov_ts_hi
      // [32]: recov_ts_lo
      // [33]: recov_fla
      // [34]: recov_otp
      // [35]: recov_ot0
      // [36]: recov_ot1
      // [37]: recov_ot2
      // [38]: recov_ot3
      // [39]: recov_ot4
      // [40]: recov_ot5
      .alert_tx_o  ( alert_tx[40:28] ),
      .alert_rx_i  ( alert_rx[40:28] ),

      // Inter-module signals
      .ast_alert_i(sensor_ctrl_ast_alert_req_i),
      .ast_alert_o(sensor_ctrl_ast_alert_rsp_o),
      .ast_status_i(sensor_ctrl_ast_status_i),
      .ast_init_done_i(ast_init_done_i),
      .ast2pinmux_i(ast2pinmux_i),
      .tl_i(sensor_ctrl_aon_tl_req),
      .tl_o(sensor_ctrl_aon_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel])
  );

  sram_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[42:41]),
    .RndCnstSramKey(RndCnstSramCtrlRetAonSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlRetAonSramNonce),
    .RndCnstSramLfsrPerm(RndCnstSramCtrlRetAonSramLfsrPerm),
    .MemSizeRam(4096),
    .InstrExec(SramCtrlRetAonInstrExec)
  ) u_sram_ctrl_ret_aon (
      // [41]: fatal_intg_error
      // [42]: fatal_parity_error
      .alert_tx_o  ( alert_tx[42:41] ),
      .alert_rx_i  ( alert_rx[42:41] ),

      // Inter-module signals
      .sram_otp_key_o(otp_ctrl_sram_otp_key_req[1]),
      .sram_otp_key_i(otp_ctrl_sram_otp_key_rsp[1]),
      .cfg_i(ast_ram_1p_cfg),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en),
      .otp_en_sram_ifetch_i(sram_ctrl_ret_aon_otp_en_sram_ifetch),
      .regs_tl_i(sram_ctrl_ret_aon_regs_tl_req),
      .regs_tl_o(sram_ctrl_ret_aon_regs_tl_rsp),
      .ram_tl_i(sram_ctrl_ret_aon_ram_tl_req),
      .ram_tl_o(sram_ctrl_ret_aon_ram_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_io_div4_infra),
      .clk_otp_i (clkmgr_aon_clocks.clk_io_div4_infra),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_otp_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel])
  );

  flash_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[46:43]),
    .RndCnstAddrKey(RndCnstFlashCtrlAddrKey),
    .RndCnstDataKey(RndCnstFlashCtrlDataKey),
    .RndCnstLfsrSeed(RndCnstFlashCtrlLfsrSeed),
    .RndCnstLfsrPerm(RndCnstFlashCtrlLfsrPerm)
  ) u_flash_ctrl (

      // Input
      .cio_tck_i    (cio_flash_ctrl_tck_p2d),
      .cio_tms_i    (cio_flash_ctrl_tms_p2d),
      .cio_tdi_i    (cio_flash_ctrl_tdi_p2d),

      // Output
      .cio_tdo_o    (cio_flash_ctrl_tdo_d2p),
      .cio_tdo_en_o (cio_flash_ctrl_tdo_en_d2p),

      // Interrupt
      .intr_prog_empty_o (intr_flash_ctrl_prog_empty),
      .intr_prog_lvl_o   (intr_flash_ctrl_prog_lvl),
      .intr_rd_full_o    (intr_flash_ctrl_rd_full),
      .intr_rd_lvl_o     (intr_flash_ctrl_rd_lvl),
      .intr_op_done_o    (intr_flash_ctrl_op_done),
      .intr_err_o        (intr_flash_ctrl_err),
      // [43]: recov_err
      // [44]: recov_mp_err
      // [45]: recov_ecc_err
      // [46]: fatal_intg_err
      .alert_tx_o  ( alert_tx[46:43] ),
      .alert_rx_i  ( alert_rx[46:43] ),

      // Inter-module signals
      .flash_o(flash_ctrl_flash_req),
      .flash_i(flash_ctrl_flash_rsp),
      .otp_o(flash_ctrl_otp_req),
      .otp_i(flash_ctrl_otp_rsp),
      .lc_creator_seed_sw_rw_en_i(lc_ctrl_lc_creator_seed_sw_rw_en),
      .lc_owner_seed_sw_rw_en_i(lc_ctrl_lc_owner_seed_sw_rw_en),
      .lc_iso_part_sw_rd_en_i(lc_ctrl_lc_iso_part_sw_rd_en),
      .lc_iso_part_sw_wr_en_i(lc_ctrl_lc_iso_part_sw_wr_en),
      .lc_seed_hw_rd_en_i(lc_ctrl_lc_seed_hw_rd_en),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .rma_req_i(flash_ctrl_rma_req),
      .rma_ack_o(flash_ctrl_rma_ack),
      .rma_seed_i(flash_ctrl_rma_seed),
      .pwrmgr_o(pwrmgr_aon_pwr_flash),
      .keymgr_o(flash_ctrl_keymgr),
      .core_tl_i(flash_ctrl_core_tl_req),
      .core_tl_o(flash_ctrl_core_tl_rsp),
      .prim_tl_i(flash_ctrl_prim_tl_req),
      .prim_tl_o(flash_ctrl_prim_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_infra),
      .clk_otp_i (clkmgr_aon_clocks.clk_io_div4_infra),
      .rst_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
      .rst_otp_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  rv_dm #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[47:47]),
    .IdcodeValue(RvDmIdcodeValue)
  ) u_rv_dm (
      // [47]: fatal_fault
      .alert_tx_o  ( alert_tx[47:47] ),
      .alert_rx_i  ( alert_rx[47:47] ),

      // Inter-module signals
      .jtag_i(pinmux_aon_rv_jtag_req),
      .jtag_o(pinmux_aon_rv_jtag_rsp),
      .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en),
      .unavailable_i(1'b0),
      .ndmreset_req_o(rv_dm_ndmreset_req),
      .dmactive_o(),
      .debug_req_o(rv_dm_debug_req),
      .sba_tl_h_o(main_tl_rv_dm__sba_req),
      .sba_tl_h_i(main_tl_rv_dm__sba_rsp),
      .regs_tl_d_i(rv_dm_regs_tl_d_req),
      .regs_tl_d_o(rv_dm_regs_tl_d_rsp),
      .rom_tl_d_i(rv_dm_rom_tl_d_req),
      .rom_tl_d_o(rv_dm_rom_tl_d_rsp),
      .scanmode_i,
      .scan_rst_ni,

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_infra),
      .rst_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel])
  );

  rv_plic #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[48:48])
  ) u_rv_plic (
      // [48]: fatal_fault
      .alert_tx_o  ( alert_tx[48:48] ),
      .alert_rx_i  ( alert_rx[48:48] ),

      // Inter-module signals
      .tl_i(rv_plic_tl_req),
      .tl_o(rv_plic_tl_rsp),

      .intr_src_i (intr_vector),
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  aes #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[50:49]),
    .AES192Enable(1'b1),
    .Masking(AesMasking),
    .SBoxImpl(AesSBoxImpl),
    .SecStartTriggerDelay(SecAesStartTriggerDelay),
    .SecAllowForcingMasks(SecAesAllowForcingMasks),
    .SecSkipPRNGReseeding(SecAesSkipPRNGReseeding),
    .RndCnstClearingLfsrSeed(RndCnstAesClearingLfsrSeed),
    .RndCnstClearingLfsrPerm(RndCnstAesClearingLfsrPerm),
    .RndCnstClearingSharePerm(RndCnstAesClearingSharePerm),
    .RndCnstMaskingLfsrSeed(RndCnstAesMaskingLfsrSeed),
    .RndCnstMskgChunkLfsrPerm(RndCnstAesMskgChunkLfsrPerm)
  ) u_aes (
      // [49]: recov_ctrl_update_err
      // [50]: fatal_fault
      .alert_tx_o  ( alert_tx[50:49] ),
      .alert_rx_i  ( alert_rx[50:49] ),

      // Inter-module signals
      .idle_o(clkmgr_aon_idle[0]),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .edn_o(edn0_edn_req[5]),
      .edn_i(edn0_edn_rsp[5]),
      .tl_i(aes_tl_req),
      .tl_o(aes_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_aes),
      .clk_edn_i (clkmgr_aon_clocks.clk_main_aes),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  hmac #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[51:51])
  ) u_hmac (

      // Interrupt
      .intr_hmac_done_o  (intr_hmac_hmac_done),
      .intr_fifo_empty_o (intr_hmac_fifo_empty),
      .intr_hmac_err_o   (intr_hmac_hmac_err),
      // [51]: fatal_fault
      .alert_tx_o  ( alert_tx[51:51] ),
      .alert_rx_i  ( alert_rx[51:51] ),

      // Inter-module signals
      .idle_o(clkmgr_aon_idle[1]),
      .tl_i(hmac_tl_req),
      .tl_o(hmac_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_hmac),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  kmac #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[52:52]),
    .EnMasking(KmacEnMasking),
    .ReuseShare(KmacReuseShare)
  ) u_kmac (

      // Interrupt
      .intr_kmac_done_o  (intr_kmac_kmac_done),
      .intr_fifo_empty_o (intr_kmac_fifo_empty),
      .intr_kmac_err_o   (intr_kmac_kmac_err),
      // [52]: fatal_fault
      .alert_tx_o  ( alert_tx[52:52] ),
      .alert_rx_i  ( alert_rx[52:52] ),

      // Inter-module signals
      .keymgr_key_i(keymgr_kmac_key),
      .app_i(kmac_app_req),
      .app_o(kmac_app_rsp),
      .entropy_o(edn0_edn_req[3]),
      .entropy_i(edn0_edn_rsp[3]),
      .idle_o(clkmgr_aon_idle[2]),
      .tl_i(kmac_tl_req),
      .tl_o(kmac_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_kmac),
      .clk_edn_i (clkmgr_aon_clocks.clk_main_kmac),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  keymgr #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[54:53]),
    .RndCnstLfsrSeed(RndCnstKeymgrLfsrSeed),
    .RndCnstLfsrPerm(RndCnstKeymgrLfsrPerm),
    .RndCnstRandPerm(RndCnstKeymgrRandPerm),
    .RndCnstRevisionSeed(RndCnstKeymgrRevisionSeed),
    .RndCnstCreatorIdentitySeed(RndCnstKeymgrCreatorIdentitySeed),
    .RndCnstOwnerIntIdentitySeed(RndCnstKeymgrOwnerIntIdentitySeed),
    .RndCnstOwnerIdentitySeed(RndCnstKeymgrOwnerIdentitySeed),
    .RndCnstSoftOutputSeed(RndCnstKeymgrSoftOutputSeed),
    .RndCnstHardOutputSeed(RndCnstKeymgrHardOutputSeed),
    .RndCnstAesSeed(RndCnstKeymgrAesSeed),
    .RndCnstHmacSeed(RndCnstKeymgrHmacSeed),
    .RndCnstKmacSeed(RndCnstKeymgrKmacSeed),
    .RndCnstOtbnSeed(RndCnstKeymgrOtbnSeed),
    .RndCnstNoneSeed(RndCnstKeymgrNoneSeed)
  ) u_keymgr (

      // Interrupt
      .intr_op_done_o (intr_keymgr_op_done),
      // [53]: fatal_fault_err
      // [54]: recov_operation_err
      .alert_tx_o  ( alert_tx[54:53] ),
      .alert_rx_i  ( alert_rx[54:53] ),

      // Inter-module signals
      .edn_o(edn0_edn_req[0]),
      .edn_i(edn0_edn_rsp[0]),
      .aes_key_o(),
      .hmac_key_o(),
      .kmac_key_o(keymgr_kmac_key),
      .otbn_key_o(),
      .kmac_data_o(kmac_app_req[0]),
      .kmac_data_i(kmac_app_rsp[0]),
      .otp_key_i(otp_ctrl_otp_keymgr_key),
      .otp_device_id_i(keymgr_otp_device_id),
      .flash_i(flash_ctrl_keymgr),
      .lc_keymgr_en_i(lc_ctrl_lc_keymgr_en),
      .lc_keymgr_div_i(lc_ctrl_lc_keymgr_div),
      .rom_digest_i(rom_ctrl_keymgr_data),
      .tl_i(keymgr_tl_req),
      .tl_o(keymgr_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .clk_edn_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  csrng #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[55:55]),
    .RndCnstCsKeymgrDivNonProduction(RndCnstCsrngCsKeymgrDivNonProduction),
    .RndCnstCsKeymgrDivProduction(RndCnstCsrngCsKeymgrDivProduction),
    .SBoxImpl(CsrngSBoxImpl)
  ) u_csrng (

      // Interrupt
      .intr_cs_cmd_req_done_o (intr_csrng_cs_cmd_req_done),
      .intr_cs_entropy_req_o  (intr_csrng_cs_entropy_req),
      .intr_cs_hw_inst_exc_o  (intr_csrng_cs_hw_inst_exc),
      .intr_cs_fatal_err_o    (intr_csrng_cs_fatal_err),
      // [55]: fatal_alert
      .alert_tx_o  ( alert_tx[55:55] ),
      .alert_rx_i  ( alert_rx[55:55] ),

      // Inter-module signals
      .csrng_cmd_i(csrng_csrng_cmd_req),
      .csrng_cmd_o(csrng_csrng_cmd_rsp),
      .entropy_src_hw_if_o(csrng_entropy_src_hw_if_req),
      .entropy_src_hw_if_i(csrng_entropy_src_hw_if_rsp),
      .cs_aes_halt_i(csrng_cs_aes_halt_req),
      .cs_aes_halt_o(csrng_cs_aes_halt_rsp),
      .otp_en_csrng_sw_app_read_i(csrng_otp_en_csrng_sw_app_read),
      .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en),
      .tl_i(csrng_tl_req),
      .tl_o(csrng_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  entropy_src #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[57:56]),
    .Stub(EntropySrcStub)
  ) u_entropy_src (

      // Interrupt
      .intr_es_entropy_valid_o      (intr_entropy_src_es_entropy_valid),
      .intr_es_health_test_failed_o (intr_entropy_src_es_health_test_failed),
      .intr_es_observe_fifo_ready_o (intr_entropy_src_es_observe_fifo_ready),
      .intr_es_fatal_err_o          (intr_entropy_src_es_fatal_err),
      // [56]: recov_alert
      // [57]: fatal_alert
      .alert_tx_o  ( alert_tx[57:56] ),
      .alert_rx_i  ( alert_rx[57:56] ),

      // Inter-module signals
      .entropy_src_hw_if_i(csrng_entropy_src_hw_if_req),
      .entropy_src_hw_if_o(csrng_entropy_src_hw_if_rsp),
      .cs_aes_halt_o(csrng_cs_aes_halt_req),
      .cs_aes_halt_i(csrng_cs_aes_halt_rsp),
      .entropy_src_rng_o(es_rng_req_o),
      .entropy_src_rng_i(es_rng_rsp_i),
      .entropy_src_xht_o(),
      .entropy_src_xht_i(entropy_src_pkg::ENTROPY_SRC_XHT_RSP_DEFAULT),
      .otp_en_entropy_src_fw_read_i(entropy_src_otp_en_entropy_src_fw_read),
      .otp_en_entropy_src_fw_over_i(entropy_src_otp_en_entropy_src_fw_over),
      .rng_fips_o(es_rng_fips_o),
      .tl_i(entropy_src_tl_req),
      .tl_o(entropy_src_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  edn #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[58:58])
  ) u_edn0 (

      // Interrupt
      .intr_edn_cmd_req_done_o (intr_edn0_edn_cmd_req_done),
      .intr_edn_fatal_err_o    (intr_edn0_edn_fatal_err),
      // [58]: fatal_alert
      .alert_tx_o  ( alert_tx[58:58] ),
      .alert_rx_i  ( alert_rx[58:58] ),

      // Inter-module signals
      .csrng_cmd_o(csrng_csrng_cmd_req[0]),
      .csrng_cmd_i(csrng_csrng_cmd_rsp[0]),
      .edn_i(edn0_edn_req),
      .edn_o(edn0_edn_rsp),
      .tl_i(edn0_tl_req),
      .tl_o(edn0_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  edn #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[59:59])
  ) u_edn1 (

      // Interrupt
      .intr_edn_cmd_req_done_o (intr_edn1_edn_cmd_req_done),
      .intr_edn_fatal_err_o    (intr_edn1_edn_fatal_err),
      // [59]: fatal_alert
      .alert_tx_o  ( alert_tx[59:59] ),
      .alert_rx_i  ( alert_rx[59:59] ),

      // Inter-module signals
      .csrng_cmd_o(csrng_csrng_cmd_req[1]),
      .csrng_cmd_i(csrng_csrng_cmd_rsp[1]),
      .edn_i(edn1_edn_req),
      .edn_o(edn1_edn_rsp),
      .tl_i(edn1_tl_req),
      .tl_o(edn1_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  sram_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[61:60]),
    .RndCnstSramKey(RndCnstSramCtrlMainSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlMainSramNonce),
    .RndCnstSramLfsrPerm(RndCnstSramCtrlMainSramLfsrPerm),
    .MemSizeRam(131072),
    .InstrExec(SramCtrlMainInstrExec)
  ) u_sram_ctrl_main (
      // [60]: fatal_intg_error
      // [61]: fatal_parity_error
      .alert_tx_o  ( alert_tx[61:60] ),
      .alert_rx_i  ( alert_rx[61:60] ),

      // Inter-module signals
      .sram_otp_key_o(otp_ctrl_sram_otp_key_req[0]),
      .sram_otp_key_i(otp_ctrl_sram_otp_key_rsp[0]),
      .cfg_i(ast_ram_1p_cfg),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .lc_hw_debug_en_i(lc_ctrl_lc_hw_debug_en),
      .otp_en_sram_ifetch_i(sram_ctrl_main_otp_en_sram_ifetch),
      .regs_tl_i(sram_ctrl_main_regs_tl_req),
      .regs_tl_o(sram_ctrl_main_regs_tl_rsp),
      .ram_tl_i(sram_ctrl_main_ram_tl_req),
      .ram_tl_o(sram_ctrl_main_ram_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .clk_otp_i (clkmgr_aon_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_otp_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  otbn #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[63:62]),
    .Stub(OtbnStub),
    .RegFile(OtbnRegFile),
    .RndCnstUrndLfsrSeed(RndCnstOtbnUrndLfsrSeed),
    .RndCnstUrndChunkLfsrPerm(RndCnstOtbnUrndChunkLfsrPerm),
    .RndCnstOtbnKey(RndCnstOtbnOtbnKey),
    .RndCnstOtbnNonce(RndCnstOtbnOtbnNonce)
  ) u_otbn (

      // Interrupt
      .intr_done_o (intr_otbn_done),
      // [62]: fatal
      // [63]: recov
      .alert_tx_o  ( alert_tx[63:62] ),
      .alert_rx_i  ( alert_rx[63:62] ),

      // Inter-module signals
      .otbn_otp_key_o(otp_ctrl_otbn_otp_key_req),
      .otbn_otp_key_i(otp_ctrl_otbn_otp_key_rsp),
      .edn_rnd_o(edn1_edn_req[0]),
      .edn_rnd_i(edn1_edn_rsp[0]),
      .edn_urnd_o(edn0_edn_req[6]),
      .edn_urnd_i(edn0_edn_rsp[6]),
      .idle_o(clkmgr_aon_idle[3]),
      .ram_cfg_i(ast_ram_1p_cfg),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .tl_i(otbn_tl_req),
      .tl_o(otbn_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_otbn),
      .clk_edn_i (clkmgr_aon_clocks.clk_main_otbn),
      .clk_otp_i (clkmgr_aon_clocks.clk_io_div4_otbn),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_otp_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  rom_ctrl #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[64:64]),
    .BootRomInitFile(RomCtrlBootRomInitFile),
    .RndCnstScrNonce(RndCnstRomCtrlScrNonce),
    .RndCnstScrKey(RndCnstRomCtrlScrKey)
  ) u_rom_ctrl (
      // [64]: fatal
      .alert_tx_o  ( alert_tx[64:64] ),
      .alert_rx_i  ( alert_rx[64:64] ),

      // Inter-module signals
      .rom_cfg_i(ast_rom_cfg),
      .pwrmgr_data_o(rom_ctrl_pwrmgr_data),
      .keymgr_data_o(rom_ctrl_keymgr_data),
      .kmac_data_o(kmac_app_req[2]),
      .kmac_data_i(kmac_app_rsp[2]),
      .regs_tl_i(rom_ctrl_regs_tl_req),
      .regs_tl_o(rom_ctrl_regs_tl_rsp),
      .rom_tl_i(rom_ctrl_rom_tl_req),
      .rom_tl_o(rom_ctrl_rom_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_infra),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  rv_core_ibex_peri #(
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[68:65])
  ) u_rv_core_ibex_peri (
      // [65]: fatal_sw_err
      // [66]: recov_sw_err
      // [67]: fatal_hw_err
      // [68]: recov_hw_err
      .alert_tx_o  ( alert_tx[68:65] ),
      .alert_rx_i  ( alert_rx[68:65] ),

      // Inter-module signals
      .fatal_intg_event_i(rv_core_ibex_fatal_intg_event),
      .fatal_core_event_i(rv_core_ibex_fatal_core_event),
      .recov_core_event_i(rv_core_ibex_recov_core_event),
      .ibus_region_cfg_o(rv_core_ibex_peri_ibus_region_cfg),
      .dbus_region_cfg_o(rv_core_ibex_peri_dbus_region_cfg),
      .tl_i(rv_core_ibex_peri_tl_req),
      .tl_o(rv_core_ibex_peri_tl_rsp),

      // Clock and reset connections
      .clk_i (clkmgr_aon_clocks.clk_main_infra),
      .rst_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  // interrupt assignments
  assign intr_vector = {
      intr_otbn_done, // IDs [179 +: 1]
      intr_edn1_edn_fatal_err, // IDs [178 +: 1]
      intr_edn1_edn_cmd_req_done, // IDs [177 +: 1]
      intr_edn0_edn_fatal_err, // IDs [176 +: 1]
      intr_edn0_edn_cmd_req_done, // IDs [175 +: 1]
      intr_entropy_src_es_fatal_err, // IDs [174 +: 1]
      intr_entropy_src_es_observe_fifo_ready, // IDs [173 +: 1]
      intr_entropy_src_es_health_test_failed, // IDs [172 +: 1]
      intr_entropy_src_es_entropy_valid, // IDs [171 +: 1]
      intr_csrng_cs_fatal_err, // IDs [170 +: 1]
      intr_csrng_cs_hw_inst_exc, // IDs [169 +: 1]
      intr_csrng_cs_entropy_req, // IDs [168 +: 1]
      intr_csrng_cs_cmd_req_done, // IDs [167 +: 1]
      intr_keymgr_op_done, // IDs [166 +: 1]
      intr_kmac_kmac_err, // IDs [165 +: 1]
      intr_kmac_fifo_empty, // IDs [164 +: 1]
      intr_kmac_kmac_done, // IDs [163 +: 1]
      intr_hmac_hmac_err, // IDs [162 +: 1]
      intr_hmac_fifo_empty, // IDs [161 +: 1]
      intr_hmac_hmac_done, // IDs [160 +: 1]
      intr_flash_ctrl_err, // IDs [159 +: 1]
      intr_flash_ctrl_op_done, // IDs [158 +: 1]
      intr_flash_ctrl_rd_lvl, // IDs [157 +: 1]
      intr_flash_ctrl_rd_full, // IDs [156 +: 1]
      intr_flash_ctrl_prog_lvl, // IDs [155 +: 1]
      intr_flash_ctrl_prog_empty, // IDs [154 +: 1]
      intr_aon_timer_aon_wdog_timer_bark, // IDs [153 +: 1]
      intr_aon_timer_aon_wkup_timer_expired, // IDs [152 +: 1]
      intr_adc_ctrl_aon_debug_cable, // IDs [151 +: 1]
      intr_sysrst_ctrl_aon_sysrst_ctrl, // IDs [150 +: 1]
      intr_pwrmgr_aon_wakeup, // IDs [149 +: 1]
      intr_alert_handler_classd, // IDs [148 +: 1]
      intr_alert_handler_classc, // IDs [147 +: 1]
      intr_alert_handler_classb, // IDs [146 +: 1]
      intr_alert_handler_classa, // IDs [145 +: 1]
      intr_otp_ctrl_otp_error, // IDs [144 +: 1]
      intr_otp_ctrl_otp_operation_done, // IDs [143 +: 1]
      intr_usbdev_link_out_err, // IDs [142 +: 1]
      intr_usbdev_connected, // IDs [141 +: 1]
      intr_usbdev_frame, // IDs [140 +: 1]
      intr_usbdev_rx_bitstuff_err, // IDs [139 +: 1]
      intr_usbdev_rx_pid_err, // IDs [138 +: 1]
      intr_usbdev_rx_crc_err, // IDs [137 +: 1]
      intr_usbdev_link_in_err, // IDs [136 +: 1]
      intr_usbdev_av_overflow, // IDs [135 +: 1]
      intr_usbdev_rx_full, // IDs [134 +: 1]
      intr_usbdev_av_empty, // IDs [133 +: 1]
      intr_usbdev_link_resume, // IDs [132 +: 1]
      intr_usbdev_link_suspend, // IDs [131 +: 1]
      intr_usbdev_link_reset, // IDs [130 +: 1]
      intr_usbdev_host_lost, // IDs [129 +: 1]
      intr_usbdev_disconnected, // IDs [128 +: 1]
      intr_usbdev_pkt_sent, // IDs [127 +: 1]
      intr_usbdev_pkt_received, // IDs [126 +: 1]
      intr_rv_timer_timer_expired_0_0, // IDs [125 +: 1]
      intr_pattgen_done_ch1, // IDs [124 +: 1]
      intr_pattgen_done_ch0, // IDs [123 +: 1]
      intr_i2c2_host_timeout, // IDs [122 +: 1]
      intr_i2c2_ack_stop, // IDs [121 +: 1]
      intr_i2c2_acq_overflow, // IDs [120 +: 1]
      intr_i2c2_tx_overflow, // IDs [119 +: 1]
      intr_i2c2_tx_nonempty, // IDs [118 +: 1]
      intr_i2c2_tx_empty, // IDs [117 +: 1]
      intr_i2c2_trans_complete, // IDs [116 +: 1]
      intr_i2c2_sda_unstable, // IDs [115 +: 1]
      intr_i2c2_stretch_timeout, // IDs [114 +: 1]
      intr_i2c2_sda_interference, // IDs [113 +: 1]
      intr_i2c2_scl_interference, // IDs [112 +: 1]
      intr_i2c2_nak, // IDs [111 +: 1]
      intr_i2c2_rx_overflow, // IDs [110 +: 1]
      intr_i2c2_fmt_overflow, // IDs [109 +: 1]
      intr_i2c2_rx_watermark, // IDs [108 +: 1]
      intr_i2c2_fmt_watermark, // IDs [107 +: 1]
      intr_i2c1_host_timeout, // IDs [106 +: 1]
      intr_i2c1_ack_stop, // IDs [105 +: 1]
      intr_i2c1_acq_overflow, // IDs [104 +: 1]
      intr_i2c1_tx_overflow, // IDs [103 +: 1]
      intr_i2c1_tx_nonempty, // IDs [102 +: 1]
      intr_i2c1_tx_empty, // IDs [101 +: 1]
      intr_i2c1_trans_complete, // IDs [100 +: 1]
      intr_i2c1_sda_unstable, // IDs [99 +: 1]
      intr_i2c1_stretch_timeout, // IDs [98 +: 1]
      intr_i2c1_sda_interference, // IDs [97 +: 1]
      intr_i2c1_scl_interference, // IDs [96 +: 1]
      intr_i2c1_nak, // IDs [95 +: 1]
      intr_i2c1_rx_overflow, // IDs [94 +: 1]
      intr_i2c1_fmt_overflow, // IDs [93 +: 1]
      intr_i2c1_rx_watermark, // IDs [92 +: 1]
      intr_i2c1_fmt_watermark, // IDs [91 +: 1]
      intr_i2c0_host_timeout, // IDs [90 +: 1]
      intr_i2c0_ack_stop, // IDs [89 +: 1]
      intr_i2c0_acq_overflow, // IDs [88 +: 1]
      intr_i2c0_tx_overflow, // IDs [87 +: 1]
      intr_i2c0_tx_nonempty, // IDs [86 +: 1]
      intr_i2c0_tx_empty, // IDs [85 +: 1]
      intr_i2c0_trans_complete, // IDs [84 +: 1]
      intr_i2c0_sda_unstable, // IDs [83 +: 1]
      intr_i2c0_stretch_timeout, // IDs [82 +: 1]
      intr_i2c0_sda_interference, // IDs [81 +: 1]
      intr_i2c0_scl_interference, // IDs [80 +: 1]
      intr_i2c0_nak, // IDs [79 +: 1]
      intr_i2c0_rx_overflow, // IDs [78 +: 1]
      intr_i2c0_fmt_overflow, // IDs [77 +: 1]
      intr_i2c0_rx_watermark, // IDs [76 +: 1]
      intr_i2c0_fmt_watermark, // IDs [75 +: 1]
      intr_spi_host1_spi_event, // IDs [74 +: 1]
      intr_spi_host1_error, // IDs [73 +: 1]
      intr_spi_host0_spi_event, // IDs [72 +: 1]
      intr_spi_host0_error, // IDs [71 +: 1]
      intr_spi_device_txunderflow, // IDs [70 +: 1]
      intr_spi_device_rxoverflow, // IDs [69 +: 1]
      intr_spi_device_rxerr, // IDs [68 +: 1]
      intr_spi_device_txlvl, // IDs [67 +: 1]
      intr_spi_device_rxlvl, // IDs [66 +: 1]
      intr_spi_device_rxf, // IDs [65 +: 1]
      intr_gpio_gpio, // IDs [33 +: 32]
      intr_uart3_rx_parity_err, // IDs [32 +: 1]
      intr_uart3_rx_timeout, // IDs [31 +: 1]
      intr_uart3_rx_break_err, // IDs [30 +: 1]
      intr_uart3_rx_frame_err, // IDs [29 +: 1]
      intr_uart3_rx_overflow, // IDs [28 +: 1]
      intr_uart3_tx_empty, // IDs [27 +: 1]
      intr_uart3_rx_watermark, // IDs [26 +: 1]
      intr_uart3_tx_watermark, // IDs [25 +: 1]
      intr_uart2_rx_parity_err, // IDs [24 +: 1]
      intr_uart2_rx_timeout, // IDs [23 +: 1]
      intr_uart2_rx_break_err, // IDs [22 +: 1]
      intr_uart2_rx_frame_err, // IDs [21 +: 1]
      intr_uart2_rx_overflow, // IDs [20 +: 1]
      intr_uart2_tx_empty, // IDs [19 +: 1]
      intr_uart2_rx_watermark, // IDs [18 +: 1]
      intr_uart2_tx_watermark, // IDs [17 +: 1]
      intr_uart1_rx_parity_err, // IDs [16 +: 1]
      intr_uart1_rx_timeout, // IDs [15 +: 1]
      intr_uart1_rx_break_err, // IDs [14 +: 1]
      intr_uart1_rx_frame_err, // IDs [13 +: 1]
      intr_uart1_rx_overflow, // IDs [12 +: 1]
      intr_uart1_tx_empty, // IDs [11 +: 1]
      intr_uart1_rx_watermark, // IDs [10 +: 1]
      intr_uart1_tx_watermark, // IDs [9 +: 1]
      intr_uart0_rx_parity_err, // IDs [8 +: 1]
      intr_uart0_rx_timeout, // IDs [7 +: 1]
      intr_uart0_rx_break_err, // IDs [6 +: 1]
      intr_uart0_rx_frame_err, // IDs [5 +: 1]
      intr_uart0_rx_overflow, // IDs [4 +: 1]
      intr_uart0_tx_empty, // IDs [3 +: 1]
      intr_uart0_rx_watermark, // IDs [2 +: 1]
      intr_uart0_tx_watermark, // IDs [1 +: 1]
      1'b 0 // ID [0 +: 1] is a special case and tied to zero.
  };

  // TL-UL Crossbar
  xbar_main u_xbar_main (
    .clk_main_i (clkmgr_aon_clocks.clk_main_infra),
    .clk_fixed_i (clkmgr_aon_clocks.clk_io_div4_infra),
    .rst_main_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_fixed_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),

    // port: tl_corei
    .tl_corei_i(main_tl_corei_req),
    .tl_corei_o(main_tl_corei_rsp),

    // port: tl_cored
    .tl_cored_i(main_tl_cored_req),
    .tl_cored_o(main_tl_cored_rsp),

    // port: tl_rv_dm__sba
    .tl_rv_dm__sba_i(main_tl_rv_dm__sba_req),
    .tl_rv_dm__sba_o(main_tl_rv_dm__sba_rsp),

    // port: tl_rv_dm__regs
    .tl_rv_dm__regs_o(rv_dm_regs_tl_d_req),
    .tl_rv_dm__regs_i(rv_dm_regs_tl_d_rsp),

    // port: tl_rv_dm__rom
    .tl_rv_dm__rom_o(rv_dm_rom_tl_d_req),
    .tl_rv_dm__rom_i(rv_dm_rom_tl_d_rsp),

    // port: tl_rom_ctrl__rom
    .tl_rom_ctrl__rom_o(rom_ctrl_rom_tl_req),
    .tl_rom_ctrl__rom_i(rom_ctrl_rom_tl_rsp),

    // port: tl_rom_ctrl__regs
    .tl_rom_ctrl__regs_o(rom_ctrl_regs_tl_req),
    .tl_rom_ctrl__regs_i(rom_ctrl_regs_tl_rsp),

    // port: tl_eflash
    .tl_eflash_o(eflash_tl_req),
    .tl_eflash_i(eflash_tl_rsp),

    // port: tl_peri
    .tl_peri_o(main_tl_peri_req),
    .tl_peri_i(main_tl_peri_rsp),

    // port: tl_flash_ctrl__core
    .tl_flash_ctrl__core_o(flash_ctrl_core_tl_req),
    .tl_flash_ctrl__core_i(flash_ctrl_core_tl_rsp),

    // port: tl_flash_ctrl__prim
    .tl_flash_ctrl__prim_o(flash_ctrl_prim_tl_req),
    .tl_flash_ctrl__prim_i(flash_ctrl_prim_tl_rsp),

    // port: tl_hmac
    .tl_hmac_o(hmac_tl_req),
    .tl_hmac_i(hmac_tl_rsp),

    // port: tl_kmac
    .tl_kmac_o(kmac_tl_req),
    .tl_kmac_i(kmac_tl_rsp),

    // port: tl_aes
    .tl_aes_o(aes_tl_req),
    .tl_aes_i(aes_tl_rsp),

    // port: tl_entropy_src
    .tl_entropy_src_o(entropy_src_tl_req),
    .tl_entropy_src_i(entropy_src_tl_rsp),

    // port: tl_csrng
    .tl_csrng_o(csrng_tl_req),
    .tl_csrng_i(csrng_tl_rsp),

    // port: tl_edn0
    .tl_edn0_o(edn0_tl_req),
    .tl_edn0_i(edn0_tl_rsp),

    // port: tl_edn1
    .tl_edn1_o(edn1_tl_req),
    .tl_edn1_i(edn1_tl_rsp),

    // port: tl_rv_plic
    .tl_rv_plic_o(rv_plic_tl_req),
    .tl_rv_plic_i(rv_plic_tl_rsp),

    // port: tl_otbn
    .tl_otbn_o(otbn_tl_req),
    .tl_otbn_i(otbn_tl_rsp),

    // port: tl_keymgr
    .tl_keymgr_o(keymgr_tl_req),
    .tl_keymgr_i(keymgr_tl_rsp),

    // port: tl_rv_core_ibex_peri
    .tl_rv_core_ibex_peri_o(rv_core_ibex_peri_tl_req),
    .tl_rv_core_ibex_peri_i(rv_core_ibex_peri_tl_rsp),

    // port: tl_sram_ctrl_main__regs
    .tl_sram_ctrl_main__regs_o(sram_ctrl_main_regs_tl_req),
    .tl_sram_ctrl_main__regs_i(sram_ctrl_main_regs_tl_rsp),

    // port: tl_sram_ctrl_main__ram
    .tl_sram_ctrl_main__ram_o(sram_ctrl_main_ram_tl_req),
    .tl_sram_ctrl_main__ram_i(sram_ctrl_main_ram_tl_rsp),


    .scanmode_i
  );
  xbar_peri u_xbar_peri (
    .clk_peri_i (clkmgr_aon_clocks.clk_io_div4_infra),
    .rst_peri_ni (rstmgr_aon_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),

    // port: tl_main
    .tl_main_i(main_tl_peri_req),
    .tl_main_o(main_tl_peri_rsp),

    // port: tl_uart0
    .tl_uart0_o(uart0_tl_req),
    .tl_uart0_i(uart0_tl_rsp),

    // port: tl_uart1
    .tl_uart1_o(uart1_tl_req),
    .tl_uart1_i(uart1_tl_rsp),

    // port: tl_uart2
    .tl_uart2_o(uart2_tl_req),
    .tl_uart2_i(uart2_tl_rsp),

    // port: tl_uart3
    .tl_uart3_o(uart3_tl_req),
    .tl_uart3_i(uart3_tl_rsp),

    // port: tl_i2c0
    .tl_i2c0_o(i2c0_tl_req),
    .tl_i2c0_i(i2c0_tl_rsp),

    // port: tl_i2c1
    .tl_i2c1_o(i2c1_tl_req),
    .tl_i2c1_i(i2c1_tl_rsp),

    // port: tl_i2c2
    .tl_i2c2_o(i2c2_tl_req),
    .tl_i2c2_i(i2c2_tl_rsp),

    // port: tl_pattgen
    .tl_pattgen_o(pattgen_tl_req),
    .tl_pattgen_i(pattgen_tl_rsp),

    // port: tl_pwm_aon
    .tl_pwm_aon_o(pwm_aon_tl_req),
    .tl_pwm_aon_i(pwm_aon_tl_rsp),

    // port: tl_gpio
    .tl_gpio_o(gpio_tl_req),
    .tl_gpio_i(gpio_tl_rsp),

    // port: tl_spi_device
    .tl_spi_device_o(spi_device_tl_req),
    .tl_spi_device_i(spi_device_tl_rsp),

    // port: tl_spi_host0
    .tl_spi_host0_o(spi_host0_tl_req),
    .tl_spi_host0_i(spi_host0_tl_rsp),

    // port: tl_spi_host1
    .tl_spi_host1_o(spi_host1_tl_req),
    .tl_spi_host1_i(spi_host1_tl_rsp),

    // port: tl_rv_timer
    .tl_rv_timer_o(rv_timer_tl_req),
    .tl_rv_timer_i(rv_timer_tl_rsp),

    // port: tl_usbdev
    .tl_usbdev_o(usbdev_tl_req),
    .tl_usbdev_i(usbdev_tl_rsp),

    // port: tl_pwrmgr_aon
    .tl_pwrmgr_aon_o(pwrmgr_aon_tl_req),
    .tl_pwrmgr_aon_i(pwrmgr_aon_tl_rsp),

    // port: tl_rstmgr_aon
    .tl_rstmgr_aon_o(rstmgr_aon_tl_req),
    .tl_rstmgr_aon_i(rstmgr_aon_tl_rsp),

    // port: tl_clkmgr_aon
    .tl_clkmgr_aon_o(clkmgr_aon_tl_req),
    .tl_clkmgr_aon_i(clkmgr_aon_tl_rsp),

    // port: tl_pinmux_aon
    .tl_pinmux_aon_o(pinmux_aon_tl_req),
    .tl_pinmux_aon_i(pinmux_aon_tl_rsp),

    // port: tl_otp_ctrl
    .tl_otp_ctrl_o(otp_ctrl_tl_req),
    .tl_otp_ctrl_i(otp_ctrl_tl_rsp),

    // port: tl_lc_ctrl
    .tl_lc_ctrl_o(lc_ctrl_tl_req),
    .tl_lc_ctrl_i(lc_ctrl_tl_rsp),

    // port: tl_sensor_ctrl_aon
    .tl_sensor_ctrl_aon_o(sensor_ctrl_aon_tl_req),
    .tl_sensor_ctrl_aon_i(sensor_ctrl_aon_tl_rsp),

    // port: tl_alert_handler
    .tl_alert_handler_o(alert_handler_tl_req),
    .tl_alert_handler_i(alert_handler_tl_rsp),

    // port: tl_sram_ctrl_ret_aon__regs
    .tl_sram_ctrl_ret_aon__regs_o(sram_ctrl_ret_aon_regs_tl_req),
    .tl_sram_ctrl_ret_aon__regs_i(sram_ctrl_ret_aon_regs_tl_rsp),

    // port: tl_sram_ctrl_ret_aon__ram
    .tl_sram_ctrl_ret_aon__ram_o(sram_ctrl_ret_aon_ram_tl_req),
    .tl_sram_ctrl_ret_aon__ram_i(sram_ctrl_ret_aon_ram_tl_rsp),

    // port: tl_aon_timer_aon
    .tl_aon_timer_aon_o(aon_timer_aon_tl_req),
    .tl_aon_timer_aon_i(aon_timer_aon_tl_rsp),

    // port: tl_sysrst_ctrl_aon
    .tl_sysrst_ctrl_aon_o(sysrst_ctrl_aon_tl_req),
    .tl_sysrst_ctrl_aon_i(sysrst_ctrl_aon_tl_rsp),

    // port: tl_adc_ctrl_aon
    .tl_adc_ctrl_aon_o(adc_ctrl_aon_tl_req),
    .tl_adc_ctrl_aon_i(adc_ctrl_aon_tl_rsp),

    // port: tl_ast
    .tl_ast_o(ast_tl_req_o),
    .tl_ast_i(ast_tl_rsp_i),


    .scanmode_i
  );

  // Pinmux connections
  // All muxed inputs
  assign cio_gpio_gpio_p2d[0] = mio_p2d[MioInGpioGpio0];
  assign cio_gpio_gpio_p2d[1] = mio_p2d[MioInGpioGpio1];
  assign cio_gpio_gpio_p2d[2] = mio_p2d[MioInGpioGpio2];
  assign cio_gpio_gpio_p2d[3] = mio_p2d[MioInGpioGpio3];
  assign cio_gpio_gpio_p2d[4] = mio_p2d[MioInGpioGpio4];
  assign cio_gpio_gpio_p2d[5] = mio_p2d[MioInGpioGpio5];
  assign cio_gpio_gpio_p2d[6] = mio_p2d[MioInGpioGpio6];
  assign cio_gpio_gpio_p2d[7] = mio_p2d[MioInGpioGpio7];
  assign cio_gpio_gpio_p2d[8] = mio_p2d[MioInGpioGpio8];
  assign cio_gpio_gpio_p2d[9] = mio_p2d[MioInGpioGpio9];
  assign cio_gpio_gpio_p2d[10] = mio_p2d[MioInGpioGpio10];
  assign cio_gpio_gpio_p2d[11] = mio_p2d[MioInGpioGpio11];
  assign cio_gpio_gpio_p2d[12] = mio_p2d[MioInGpioGpio12];
  assign cio_gpio_gpio_p2d[13] = mio_p2d[MioInGpioGpio13];
  assign cio_gpio_gpio_p2d[14] = mio_p2d[MioInGpioGpio14];
  assign cio_gpio_gpio_p2d[15] = mio_p2d[MioInGpioGpio15];
  assign cio_gpio_gpio_p2d[16] = mio_p2d[MioInGpioGpio16];
  assign cio_gpio_gpio_p2d[17] = mio_p2d[MioInGpioGpio17];
  assign cio_gpio_gpio_p2d[18] = mio_p2d[MioInGpioGpio18];
  assign cio_gpio_gpio_p2d[19] = mio_p2d[MioInGpioGpio19];
  assign cio_gpio_gpio_p2d[20] = mio_p2d[MioInGpioGpio20];
  assign cio_gpio_gpio_p2d[21] = mio_p2d[MioInGpioGpio21];
  assign cio_gpio_gpio_p2d[22] = mio_p2d[MioInGpioGpio22];
  assign cio_gpio_gpio_p2d[23] = mio_p2d[MioInGpioGpio23];
  assign cio_gpio_gpio_p2d[24] = mio_p2d[MioInGpioGpio24];
  assign cio_gpio_gpio_p2d[25] = mio_p2d[MioInGpioGpio25];
  assign cio_gpio_gpio_p2d[26] = mio_p2d[MioInGpioGpio26];
  assign cio_gpio_gpio_p2d[27] = mio_p2d[MioInGpioGpio27];
  assign cio_gpio_gpio_p2d[28] = mio_p2d[MioInGpioGpio28];
  assign cio_gpio_gpio_p2d[29] = mio_p2d[MioInGpioGpio29];
  assign cio_gpio_gpio_p2d[30] = mio_p2d[MioInGpioGpio30];
  assign cio_gpio_gpio_p2d[31] = mio_p2d[MioInGpioGpio31];
  assign cio_i2c0_sda_p2d = mio_p2d[MioInI2c0Sda];
  assign cio_i2c0_scl_p2d = mio_p2d[MioInI2c0Scl];
  assign cio_i2c1_sda_p2d = mio_p2d[MioInI2c1Sda];
  assign cio_i2c1_scl_p2d = mio_p2d[MioInI2c1Scl];
  assign cio_i2c2_sda_p2d = mio_p2d[MioInI2c2Sda];
  assign cio_i2c2_scl_p2d = mio_p2d[MioInI2c2Scl];
  assign cio_spi_host1_sd_p2d[0] = mio_p2d[MioInSpiHost1Sd0];
  assign cio_spi_host1_sd_p2d[1] = mio_p2d[MioInSpiHost1Sd1];
  assign cio_spi_host1_sd_p2d[2] = mio_p2d[MioInSpiHost1Sd2];
  assign cio_spi_host1_sd_p2d[3] = mio_p2d[MioInSpiHost1Sd3];
  assign cio_uart0_rx_p2d = mio_p2d[MioInUart0Rx];
  assign cio_uart1_rx_p2d = mio_p2d[MioInUart1Rx];
  assign cio_uart2_rx_p2d = mio_p2d[MioInUart2Rx];
  assign cio_uart3_rx_p2d = mio_p2d[MioInUart3Rx];
  assign cio_flash_ctrl_tck_p2d = mio_p2d[MioInFlashCtrlTck];
  assign cio_flash_ctrl_tms_p2d = mio_p2d[MioInFlashCtrlTms];
  assign cio_flash_ctrl_tdi_p2d = mio_p2d[MioInFlashCtrlTdi];
  assign cio_sysrst_ctrl_aon_ac_present_p2d = mio_p2d[MioInSysrstCtrlAonAcPresent];
  assign cio_sysrst_ctrl_aon_ec_rst_in_l_p2d = mio_p2d[MioInSysrstCtrlAonEcRstInL];
  assign cio_sysrst_ctrl_aon_key0_in_p2d = mio_p2d[MioInSysrstCtrlAonKey0In];
  assign cio_sysrst_ctrl_aon_key1_in_p2d = mio_p2d[MioInSysrstCtrlAonKey1In];
  assign cio_sysrst_ctrl_aon_key2_in_p2d = mio_p2d[MioInSysrstCtrlAonKey2In];
  assign cio_sysrst_ctrl_aon_pwrb_in_p2d = mio_p2d[MioInSysrstCtrlAonPwrbIn];
  assign cio_sysrst_ctrl_aon_lid_open_p2d = mio_p2d[MioInSysrstCtrlAonLidOpen];

  // All muxed outputs
  assign mio_d2p[MioOutGpioGpio0] = cio_gpio_gpio_d2p[0];
  assign mio_d2p[MioOutGpioGpio1] = cio_gpio_gpio_d2p[1];
  assign mio_d2p[MioOutGpioGpio2] = cio_gpio_gpio_d2p[2];
  assign mio_d2p[MioOutGpioGpio3] = cio_gpio_gpio_d2p[3];
  assign mio_d2p[MioOutGpioGpio4] = cio_gpio_gpio_d2p[4];
  assign mio_d2p[MioOutGpioGpio5] = cio_gpio_gpio_d2p[5];
  assign mio_d2p[MioOutGpioGpio6] = cio_gpio_gpio_d2p[6];
  assign mio_d2p[MioOutGpioGpio7] = cio_gpio_gpio_d2p[7];
  assign mio_d2p[MioOutGpioGpio8] = cio_gpio_gpio_d2p[8];
  assign mio_d2p[MioOutGpioGpio9] = cio_gpio_gpio_d2p[9];
  assign mio_d2p[MioOutGpioGpio10] = cio_gpio_gpio_d2p[10];
  assign mio_d2p[MioOutGpioGpio11] = cio_gpio_gpio_d2p[11];
  assign mio_d2p[MioOutGpioGpio12] = cio_gpio_gpio_d2p[12];
  assign mio_d2p[MioOutGpioGpio13] = cio_gpio_gpio_d2p[13];
  assign mio_d2p[MioOutGpioGpio14] = cio_gpio_gpio_d2p[14];
  assign mio_d2p[MioOutGpioGpio15] = cio_gpio_gpio_d2p[15];
  assign mio_d2p[MioOutGpioGpio16] = cio_gpio_gpio_d2p[16];
  assign mio_d2p[MioOutGpioGpio17] = cio_gpio_gpio_d2p[17];
  assign mio_d2p[MioOutGpioGpio18] = cio_gpio_gpio_d2p[18];
  assign mio_d2p[MioOutGpioGpio19] = cio_gpio_gpio_d2p[19];
  assign mio_d2p[MioOutGpioGpio20] = cio_gpio_gpio_d2p[20];
  assign mio_d2p[MioOutGpioGpio21] = cio_gpio_gpio_d2p[21];
  assign mio_d2p[MioOutGpioGpio22] = cio_gpio_gpio_d2p[22];
  assign mio_d2p[MioOutGpioGpio23] = cio_gpio_gpio_d2p[23];
  assign mio_d2p[MioOutGpioGpio24] = cio_gpio_gpio_d2p[24];
  assign mio_d2p[MioOutGpioGpio25] = cio_gpio_gpio_d2p[25];
  assign mio_d2p[MioOutGpioGpio26] = cio_gpio_gpio_d2p[26];
  assign mio_d2p[MioOutGpioGpio27] = cio_gpio_gpio_d2p[27];
  assign mio_d2p[MioOutGpioGpio28] = cio_gpio_gpio_d2p[28];
  assign mio_d2p[MioOutGpioGpio29] = cio_gpio_gpio_d2p[29];
  assign mio_d2p[MioOutGpioGpio30] = cio_gpio_gpio_d2p[30];
  assign mio_d2p[MioOutGpioGpio31] = cio_gpio_gpio_d2p[31];
  assign mio_d2p[MioOutI2c0Sda] = cio_i2c0_sda_d2p;
  assign mio_d2p[MioOutI2c0Scl] = cio_i2c0_scl_d2p;
  assign mio_d2p[MioOutI2c1Sda] = cio_i2c1_sda_d2p;
  assign mio_d2p[MioOutI2c1Scl] = cio_i2c1_scl_d2p;
  assign mio_d2p[MioOutI2c2Sda] = cio_i2c2_sda_d2p;
  assign mio_d2p[MioOutI2c2Scl] = cio_i2c2_scl_d2p;
  assign mio_d2p[MioOutSpiHost1Sd0] = cio_spi_host1_sd_d2p[0];
  assign mio_d2p[MioOutSpiHost1Sd1] = cio_spi_host1_sd_d2p[1];
  assign mio_d2p[MioOutSpiHost1Sd2] = cio_spi_host1_sd_d2p[2];
  assign mio_d2p[MioOutSpiHost1Sd3] = cio_spi_host1_sd_d2p[3];
  assign mio_d2p[MioOutUart0Tx] = cio_uart0_tx_d2p;
  assign mio_d2p[MioOutUart1Tx] = cio_uart1_tx_d2p;
  assign mio_d2p[MioOutUart2Tx] = cio_uart2_tx_d2p;
  assign mio_d2p[MioOutUart3Tx] = cio_uart3_tx_d2p;
  assign mio_d2p[MioOutPattgenPda0Tx] = cio_pattgen_pda0_tx_d2p;
  assign mio_d2p[MioOutPattgenPcl0Tx] = cio_pattgen_pcl0_tx_d2p;
  assign mio_d2p[MioOutPattgenPda1Tx] = cio_pattgen_pda1_tx_d2p;
  assign mio_d2p[MioOutPattgenPcl1Tx] = cio_pattgen_pcl1_tx_d2p;
  assign mio_d2p[MioOutSpiHost1Sck] = cio_spi_host1_sck_d2p;
  assign mio_d2p[MioOutSpiHost1Csb] = cio_spi_host1_csb_d2p;
  assign mio_d2p[MioOutFlashCtrlTdo] = cio_flash_ctrl_tdo_d2p;
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut0] = cio_sensor_ctrl_aon_ast_debug_out_d2p[0];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut1] = cio_sensor_ctrl_aon_ast_debug_out_d2p[1];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut2] = cio_sensor_ctrl_aon_ast_debug_out_d2p[2];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut3] = cio_sensor_ctrl_aon_ast_debug_out_d2p[3];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut4] = cio_sensor_ctrl_aon_ast_debug_out_d2p[4];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut5] = cio_sensor_ctrl_aon_ast_debug_out_d2p[5];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut6] = cio_sensor_ctrl_aon_ast_debug_out_d2p[6];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut7] = cio_sensor_ctrl_aon_ast_debug_out_d2p[7];
  assign mio_d2p[MioOutSensorCtrlAonAstDebugOut8] = cio_sensor_ctrl_aon_ast_debug_out_d2p[8];
  assign mio_d2p[MioOutPwmAonPwm0] = cio_pwm_aon_pwm_d2p[0];
  assign mio_d2p[MioOutPwmAonPwm1] = cio_pwm_aon_pwm_d2p[1];
  assign mio_d2p[MioOutPwmAonPwm2] = cio_pwm_aon_pwm_d2p[2];
  assign mio_d2p[MioOutPwmAonPwm3] = cio_pwm_aon_pwm_d2p[3];
  assign mio_d2p[MioOutPwmAonPwm4] = cio_pwm_aon_pwm_d2p[4];
  assign mio_d2p[MioOutPwmAonPwm5] = cio_pwm_aon_pwm_d2p[5];
  assign mio_d2p[MioOutSysrstCtrlAonBatDisable] = cio_sysrst_ctrl_aon_bat_disable_d2p;
  assign mio_d2p[MioOutSysrstCtrlAonKey0Out] = cio_sysrst_ctrl_aon_key0_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlAonKey1Out] = cio_sysrst_ctrl_aon_key1_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlAonKey2Out] = cio_sysrst_ctrl_aon_key2_out_d2p;
  assign mio_d2p[MioOutSysrstCtrlAonZ3Wakeup] = cio_sysrst_ctrl_aon_z3_wakeup_d2p;

  // All muxed output enables
  assign mio_en_d2p[MioOutGpioGpio0] = cio_gpio_gpio_en_d2p[0];
  assign mio_en_d2p[MioOutGpioGpio1] = cio_gpio_gpio_en_d2p[1];
  assign mio_en_d2p[MioOutGpioGpio2] = cio_gpio_gpio_en_d2p[2];
  assign mio_en_d2p[MioOutGpioGpio3] = cio_gpio_gpio_en_d2p[3];
  assign mio_en_d2p[MioOutGpioGpio4] = cio_gpio_gpio_en_d2p[4];
  assign mio_en_d2p[MioOutGpioGpio5] = cio_gpio_gpio_en_d2p[5];
  assign mio_en_d2p[MioOutGpioGpio6] = cio_gpio_gpio_en_d2p[6];
  assign mio_en_d2p[MioOutGpioGpio7] = cio_gpio_gpio_en_d2p[7];
  assign mio_en_d2p[MioOutGpioGpio8] = cio_gpio_gpio_en_d2p[8];
  assign mio_en_d2p[MioOutGpioGpio9] = cio_gpio_gpio_en_d2p[9];
  assign mio_en_d2p[MioOutGpioGpio10] = cio_gpio_gpio_en_d2p[10];
  assign mio_en_d2p[MioOutGpioGpio11] = cio_gpio_gpio_en_d2p[11];
  assign mio_en_d2p[MioOutGpioGpio12] = cio_gpio_gpio_en_d2p[12];
  assign mio_en_d2p[MioOutGpioGpio13] = cio_gpio_gpio_en_d2p[13];
  assign mio_en_d2p[MioOutGpioGpio14] = cio_gpio_gpio_en_d2p[14];
  assign mio_en_d2p[MioOutGpioGpio15] = cio_gpio_gpio_en_d2p[15];
  assign mio_en_d2p[MioOutGpioGpio16] = cio_gpio_gpio_en_d2p[16];
  assign mio_en_d2p[MioOutGpioGpio17] = cio_gpio_gpio_en_d2p[17];
  assign mio_en_d2p[MioOutGpioGpio18] = cio_gpio_gpio_en_d2p[18];
  assign mio_en_d2p[MioOutGpioGpio19] = cio_gpio_gpio_en_d2p[19];
  assign mio_en_d2p[MioOutGpioGpio20] = cio_gpio_gpio_en_d2p[20];
  assign mio_en_d2p[MioOutGpioGpio21] = cio_gpio_gpio_en_d2p[21];
  assign mio_en_d2p[MioOutGpioGpio22] = cio_gpio_gpio_en_d2p[22];
  assign mio_en_d2p[MioOutGpioGpio23] = cio_gpio_gpio_en_d2p[23];
  assign mio_en_d2p[MioOutGpioGpio24] = cio_gpio_gpio_en_d2p[24];
  assign mio_en_d2p[MioOutGpioGpio25] = cio_gpio_gpio_en_d2p[25];
  assign mio_en_d2p[MioOutGpioGpio26] = cio_gpio_gpio_en_d2p[26];
  assign mio_en_d2p[MioOutGpioGpio27] = cio_gpio_gpio_en_d2p[27];
  assign mio_en_d2p[MioOutGpioGpio28] = cio_gpio_gpio_en_d2p[28];
  assign mio_en_d2p[MioOutGpioGpio29] = cio_gpio_gpio_en_d2p[29];
  assign mio_en_d2p[MioOutGpioGpio30] = cio_gpio_gpio_en_d2p[30];
  assign mio_en_d2p[MioOutGpioGpio31] = cio_gpio_gpio_en_d2p[31];
  assign mio_en_d2p[MioOutI2c0Sda] = cio_i2c0_sda_en_d2p;
  assign mio_en_d2p[MioOutI2c0Scl] = cio_i2c0_scl_en_d2p;
  assign mio_en_d2p[MioOutI2c1Sda] = cio_i2c1_sda_en_d2p;
  assign mio_en_d2p[MioOutI2c1Scl] = cio_i2c1_scl_en_d2p;
  assign mio_en_d2p[MioOutI2c2Sda] = cio_i2c2_sda_en_d2p;
  assign mio_en_d2p[MioOutI2c2Scl] = cio_i2c2_scl_en_d2p;
  assign mio_en_d2p[MioOutSpiHost1Sd0] = cio_spi_host1_sd_en_d2p[0];
  assign mio_en_d2p[MioOutSpiHost1Sd1] = cio_spi_host1_sd_en_d2p[1];
  assign mio_en_d2p[MioOutSpiHost1Sd2] = cio_spi_host1_sd_en_d2p[2];
  assign mio_en_d2p[MioOutSpiHost1Sd3] = cio_spi_host1_sd_en_d2p[3];
  assign mio_en_d2p[MioOutUart0Tx] = cio_uart0_tx_en_d2p;
  assign mio_en_d2p[MioOutUart1Tx] = cio_uart1_tx_en_d2p;
  assign mio_en_d2p[MioOutUart2Tx] = cio_uart2_tx_en_d2p;
  assign mio_en_d2p[MioOutUart3Tx] = cio_uart3_tx_en_d2p;
  assign mio_en_d2p[MioOutPattgenPda0Tx] = cio_pattgen_pda0_tx_en_d2p;
  assign mio_en_d2p[MioOutPattgenPcl0Tx] = cio_pattgen_pcl0_tx_en_d2p;
  assign mio_en_d2p[MioOutPattgenPda1Tx] = cio_pattgen_pda1_tx_en_d2p;
  assign mio_en_d2p[MioOutPattgenPcl1Tx] = cio_pattgen_pcl1_tx_en_d2p;
  assign mio_en_d2p[MioOutSpiHost1Sck] = cio_spi_host1_sck_en_d2p;
  assign mio_en_d2p[MioOutSpiHost1Csb] = cio_spi_host1_csb_en_d2p;
  assign mio_en_d2p[MioOutFlashCtrlTdo] = cio_flash_ctrl_tdo_en_d2p;
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut0] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[0];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut1] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[1];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut2] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[2];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut3] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[3];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut4] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[4];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut5] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[5];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut6] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[6];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut7] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[7];
  assign mio_en_d2p[MioOutSensorCtrlAonAstDebugOut8] = cio_sensor_ctrl_aon_ast_debug_out_en_d2p[8];
  assign mio_en_d2p[MioOutPwmAonPwm0] = cio_pwm_aon_pwm_en_d2p[0];
  assign mio_en_d2p[MioOutPwmAonPwm1] = cio_pwm_aon_pwm_en_d2p[1];
  assign mio_en_d2p[MioOutPwmAonPwm2] = cio_pwm_aon_pwm_en_d2p[2];
  assign mio_en_d2p[MioOutPwmAonPwm3] = cio_pwm_aon_pwm_en_d2p[3];
  assign mio_en_d2p[MioOutPwmAonPwm4] = cio_pwm_aon_pwm_en_d2p[4];
  assign mio_en_d2p[MioOutPwmAonPwm5] = cio_pwm_aon_pwm_en_d2p[5];
  assign mio_en_d2p[MioOutSysrstCtrlAonBatDisable] = cio_sysrst_ctrl_aon_bat_disable_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlAonKey0Out] = cio_sysrst_ctrl_aon_key0_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlAonKey1Out] = cio_sysrst_ctrl_aon_key1_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlAonKey2Out] = cio_sysrst_ctrl_aon_key2_out_en_d2p;
  assign mio_en_d2p[MioOutSysrstCtrlAonZ3Wakeup] = cio_sysrst_ctrl_aon_z3_wakeup_en_d2p;

  // All dedicated inputs
  logic [23:0] unused_dio_p2d;
  assign unused_dio_p2d = dio_p2d;
  assign cio_spi_host0_sd_p2d[0] = dio_p2d[DioSpiHost0Sd0];
  assign cio_spi_host0_sd_p2d[1] = dio_p2d[DioSpiHost0Sd1];
  assign cio_spi_host0_sd_p2d[2] = dio_p2d[DioSpiHost0Sd2];
  assign cio_spi_host0_sd_p2d[3] = dio_p2d[DioSpiHost0Sd3];
  assign cio_spi_device_sd_p2d[0] = dio_p2d[DioSpiDeviceSd0];
  assign cio_spi_device_sd_p2d[1] = dio_p2d[DioSpiDeviceSd1];
  assign cio_spi_device_sd_p2d[2] = dio_p2d[DioSpiDeviceSd2];
  assign cio_spi_device_sd_p2d[3] = dio_p2d[DioSpiDeviceSd3];
  assign cio_usbdev_d_p2d = dio_p2d[DioUsbdevD];
  assign cio_usbdev_dp_p2d = dio_p2d[DioUsbdevDp];
  assign cio_usbdev_dn_p2d = dio_p2d[DioUsbdevDn];
  assign cio_spi_device_sck_p2d = dio_p2d[DioSpiDeviceSck];
  assign cio_spi_device_csb_p2d = dio_p2d[DioSpiDeviceCsb];
  assign cio_usbdev_sense_p2d = dio_p2d[DioUsbdevSense];

    // All dedicated outputs
  assign dio_d2p[DioSpiHost0Sd0] = cio_spi_host0_sd_d2p[0];
  assign dio_d2p[DioSpiHost0Sd1] = cio_spi_host0_sd_d2p[1];
  assign dio_d2p[DioSpiHost0Sd2] = cio_spi_host0_sd_d2p[2];
  assign dio_d2p[DioSpiHost0Sd3] = cio_spi_host0_sd_d2p[3];
  assign dio_d2p[DioSpiDeviceSd0] = cio_spi_device_sd_d2p[0];
  assign dio_d2p[DioSpiDeviceSd1] = cio_spi_device_sd_d2p[1];
  assign dio_d2p[DioSpiDeviceSd2] = cio_spi_device_sd_d2p[2];
  assign dio_d2p[DioSpiDeviceSd3] = cio_spi_device_sd_d2p[3];
  assign dio_d2p[DioUsbdevD] = cio_usbdev_d_d2p;
  assign dio_d2p[DioUsbdevDp] = cio_usbdev_dp_d2p;
  assign dio_d2p[DioUsbdevDn] = cio_usbdev_dn_d2p;
  assign dio_d2p[DioSpiDeviceSck] = 1'b0;
  assign dio_d2p[DioSpiDeviceCsb] = 1'b0;
  assign dio_d2p[DioUsbdevSense] = 1'b0;
  assign dio_d2p[DioSpiHost0Sck] = cio_spi_host0_sck_d2p;
  assign dio_d2p[DioSpiHost0Csb] = cio_spi_host0_csb_d2p;
  assign dio_d2p[DioUsbdevSe0] = cio_usbdev_se0_d2p;
  assign dio_d2p[DioUsbdevDpPullup] = cio_usbdev_dp_pullup_d2p;
  assign dio_d2p[DioUsbdevDnPullup] = cio_usbdev_dn_pullup_d2p;
  assign dio_d2p[DioUsbdevTxModeSe] = cio_usbdev_tx_mode_se_d2p;
  assign dio_d2p[DioUsbdevSuspend] = cio_usbdev_suspend_d2p;
  assign dio_d2p[DioUsbdevRxEnable] = cio_usbdev_rx_enable_d2p;
  assign dio_d2p[DioSysrstCtrlAonEcRstOutL] = cio_sysrst_ctrl_aon_ec_rst_out_l_d2p;
  assign dio_d2p[DioSysrstCtrlAonPwrbOut] = cio_sysrst_ctrl_aon_pwrb_out_d2p;

  // All dedicated output enables
  assign dio_en_d2p[DioSpiHost0Sd0] = cio_spi_host0_sd_en_d2p[0];
  assign dio_en_d2p[DioSpiHost0Sd1] = cio_spi_host0_sd_en_d2p[1];
  assign dio_en_d2p[DioSpiHost0Sd2] = cio_spi_host0_sd_en_d2p[2];
  assign dio_en_d2p[DioSpiHost0Sd3] = cio_spi_host0_sd_en_d2p[3];
  assign dio_en_d2p[DioSpiDeviceSd0] = cio_spi_device_sd_en_d2p[0];
  assign dio_en_d2p[DioSpiDeviceSd1] = cio_spi_device_sd_en_d2p[1];
  assign dio_en_d2p[DioSpiDeviceSd2] = cio_spi_device_sd_en_d2p[2];
  assign dio_en_d2p[DioSpiDeviceSd3] = cio_spi_device_sd_en_d2p[3];
  assign dio_en_d2p[DioUsbdevD] = cio_usbdev_d_en_d2p;
  assign dio_en_d2p[DioUsbdevDp] = cio_usbdev_dp_en_d2p;
  assign dio_en_d2p[DioUsbdevDn] = cio_usbdev_dn_en_d2p;
  assign dio_en_d2p[DioSpiDeviceSck] = 1'b0;
  assign dio_en_d2p[DioSpiDeviceCsb] = 1'b0;
  assign dio_en_d2p[DioUsbdevSense] = 1'b0;
  assign dio_en_d2p[DioSpiHost0Sck] = cio_spi_host0_sck_en_d2p;
  assign dio_en_d2p[DioSpiHost0Csb] = cio_spi_host0_csb_en_d2p;
  assign dio_en_d2p[DioUsbdevSe0] = cio_usbdev_se0_en_d2p;
  assign dio_en_d2p[DioUsbdevDpPullup] = cio_usbdev_dp_pullup_en_d2p;
  assign dio_en_d2p[DioUsbdevDnPullup] = cio_usbdev_dn_pullup_en_d2p;
  assign dio_en_d2p[DioUsbdevTxModeSe] = cio_usbdev_tx_mode_se_en_d2p;
  assign dio_en_d2p[DioUsbdevSuspend] = cio_usbdev_suspend_en_d2p;
  assign dio_en_d2p[DioUsbdevRxEnable] = cio_usbdev_rx_enable_en_d2p;
  assign dio_en_d2p[DioSysrstCtrlAonEcRstOutL] = cio_sysrst_ctrl_aon_ec_rst_out_l_en_d2p;
  assign dio_en_d2p[DioSysrstCtrlAonPwrbOut] = cio_sysrst_ctrl_aon_pwrb_out_en_d2p;


  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_main_i, 0)

endmodule
