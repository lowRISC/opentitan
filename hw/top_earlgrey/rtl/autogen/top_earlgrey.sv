// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                --tpl hw/top_earlgrey/data/ \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235

module top_earlgrey #(
  // Auto-inferred parameters
  parameter bit AesMasking = 1'b1,
  parameter aes_pkg::sbox_impl_e AesSBoxImpl = aes_pkg::SBoxImplCanrightMaskedNoreuse,
  parameter int unsigned SecAesStartTriggerDelay = 0,
  parameter bit SecAesAllowForcingMasks = 1'b0,
  parameter bit KmacEnMasking = 0,
  parameter int KmacReuseShare = 0,
  parameter aes_pkg::sbox_impl_e CsrngSBoxImpl = aes_pkg::SBoxImplLut,
  parameter otbn_pkg::regfile_e OtbnRegFile = otbn_pkg::RegFileFF,

  // Manually defined parameters
  parameter ibex_pkg::regfile_e IbexRegFile = ibex_pkg::RegFileFF,
  parameter bit IbexICache = 1,
  parameter bit IbexPipeLine = 0,
  parameter     BootRomInitFile = ""
) (
  // Reset, clocks defined as part of intermodule
  input               rst_ni,

  // JTAG interface
  input               jtag_tck_i,
  input               jtag_tms_i,
  input               jtag_trst_ni,
  input               jtag_tdi_i,
  output              jtag_tdo_o,

  // Multiplexed I/O
  input        [31:0] mio_in_i,
  output logic [31:0] mio_out_o,
  output logic [31:0] mio_oe_o,
  // Dedicated I/O
  input        [14:0] dio_in_i,
  output logic [14:0] dio_out_o,
  output logic [14:0] dio_oe_o,

  // pad attributes to padring
  output logic[padctrl_reg_pkg::NMioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_o,
  output logic[padctrl_reg_pkg::NDioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_o,


  // Inter-module Signal External type
  input  logic       clk_main_i,
  input  logic       clk_io_i,
  input  logic       clk_usb_i,
  input  logic       clk_aon_i,
  input  rstmgr_pkg::rstmgr_ast_t       rstmgr_ast_i,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_pwr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_pwr_ast_rsp_i,
  input  ast_wrapper_pkg::ast_alert_req_t       sensor_ctrl_ast_alert_req_i,
  output ast_wrapper_pkg::ast_alert_rsp_t       sensor_ctrl_ast_alert_rsp_o,
  input  ast_wrapper_pkg::ast_status_t       sensor_ctrl_ast_status_i,
  output logic       usbdev_usb_ref_val_o,
  output logic       usbdev_usb_ref_pulse_o,
  output tlul_pkg::tl_h2d_t       ast_tl_req_o,
  input  tlul_pkg::tl_d2h_t       ast_tl_rsp_i,
  output otp_ctrl_pkg::otp_ast_req_t       otp_ctrl_otp_ast_pwr_seq_o,
  input  otp_ctrl_pkg::otp_ast_rsp_t       otp_ctrl_otp_ast_pwr_seq_h_i,
  input  logic       flash_bist_enable_i,
  input  logic       flash_power_down_h_i,
  input  logic       flash_power_ready_h_i,
  input  logic [1:0] flash_test_mode_a_i,
  input  logic       flash_test_voltage_h_i,
  output clkmgr_pkg::clkmgr_ast_out_t       clks_ast_o,
  output rstmgr_pkg::rstmgr_ast_out_t       rsts_ast_o,
  input               scan_rst_ni, // reset used for test mode
  input               scanmode_i   // 1 for Scan
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
  // Compile-time random constants
  import top_earlgrey_rnd_cnst_pkg::*;

  // Signals
  logic [31:0] mio_p2d;
  logic [31:0] mio_d2p;
  logic [31:0] mio_d2p_en;
  logic [14:0] dio_p2d;
  logic [14:0] dio_d2p;
  logic [14:0] dio_d2p_en;
  // uart
  logic        cio_uart_rx_p2d;
  logic        cio_uart_tx_d2p;
  logic        cio_uart_tx_en_d2p;
  // gpio
  logic [31:0] cio_gpio_gpio_p2d;
  logic [31:0] cio_gpio_gpio_d2p;
  logic [31:0] cio_gpio_gpio_en_d2p;
  // spi_device
  logic        cio_spi_device_sck_p2d;
  logic        cio_spi_device_csb_p2d;
  logic        cio_spi_device_sdi_p2d;
  logic        cio_spi_device_sdo_d2p;
  logic        cio_spi_device_sdo_en_d2p;
  // rv_timer
  // sensor_ctrl
  // otp_ctrl
  // lc_ctrl
  // alert_handler
  // nmi_gen
  // pwrmgr
  // rstmgr
  // clkmgr
  // pinmux
  // padctrl
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
  logic        cio_usbdev_d_d2p;
  logic        cio_usbdev_d_en_d2p;
  logic        cio_usbdev_dp_d2p;
  logic        cio_usbdev_dp_en_d2p;
  logic        cio_usbdev_dn_d2p;
  logic        cio_usbdev_dn_en_d2p;
  // sram_ctrl_ret
  // flash_ctrl
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


  logic [98:0]  intr_vector;
  // Interrupt source list
  logic intr_uart_tx_watermark;
  logic intr_uart_rx_watermark;
  logic intr_uart_tx_empty;
  logic intr_uart_rx_overflow;
  logic intr_uart_rx_frame_err;
  logic intr_uart_rx_break_err;
  logic intr_uart_rx_timeout;
  logic intr_uart_rx_parity_err;
  logic [31:0] intr_gpio_gpio;
  logic intr_spi_device_rxf;
  logic intr_spi_device_rxlvl;
  logic intr_spi_device_txlvl;
  logic intr_spi_device_rxerr;
  logic intr_spi_device_rxoverflow;
  logic intr_spi_device_txunderflow;
  logic intr_rv_timer_timer_expired_0_0;
  logic intr_otp_ctrl_otp_operation_done;
  logic intr_otp_ctrl_otp_error;
  logic intr_alert_handler_classa;
  logic intr_alert_handler_classb;
  logic intr_alert_handler_classc;
  logic intr_alert_handler_classd;
  logic intr_nmi_gen_esc0;
  logic intr_nmi_gen_esc1;
  logic intr_nmi_gen_esc2;
  logic intr_pwrmgr_wakeup;
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
  logic intr_flash_ctrl_prog_empty;
  logic intr_flash_ctrl_prog_lvl;
  logic intr_flash_ctrl_rd_full;
  logic intr_flash_ctrl_rd_lvl;
  logic intr_flash_ctrl_op_done;
  logic intr_flash_ctrl_op_error;
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
  logic intr_csrng_cs_fifo_err;
  logic intr_entropy_src_es_entropy_valid;
  logic intr_entropy_src_es_health_test_failed;
  logic intr_entropy_src_es_fifo_err;
  logic intr_edn0_edn_cmd_req_done;
  logic intr_edn0_edn_fifo_err;
  logic intr_edn1_edn_cmd_req_done;
  logic intr_edn1_edn_fifo_err;
  logic intr_otbn_done;



  logic [0:0] irq_plic;
  logic [0:0] msip;
  logic [6:0] irq_id[1];
  logic [6:0] unused_irq_id[1];

  // this avoids lint errors
  assign unused_irq_id = irq_id;

  // Alert list
  prim_alert_pkg::alert_tx_t [alert_pkg::NAlerts-1:0]  alert_tx;
  prim_alert_pkg::alert_rx_t [alert_pkg::NAlerts-1:0]  alert_rx;


  // define inter-module signals
  alert_pkg::alert_crashdump_t       alert_handler_crashdump;
  prim_esc_pkg::esc_rx_t [3:0] alert_handler_esc_rx;
  prim_esc_pkg::esc_tx_t [3:0] alert_handler_esc_tx;
  csrng_pkg::csrng_req_t [1:0] csrng_csrng_cmd_req;
  csrng_pkg::csrng_rsp_t [1:0] csrng_csrng_cmd_rsp;
  entropy_src_pkg::entropy_src_hw_if_req_t       csrng_entropy_src_hw_if_req;
  entropy_src_pkg::entropy_src_hw_if_rsp_t       csrng_entropy_src_hw_if_rsp;
  flash_ctrl_pkg::flash_req_t       flash_ctrl_flash_req;
  flash_ctrl_pkg::flash_rsp_t       flash_ctrl_flash_rsp;
  flash_ctrl_pkg::keymgr_flash_t       flash_ctrl_keymgr;
  otp_ctrl_pkg::flash_otp_key_req_t       flash_ctrl_otp_req;
  otp_ctrl_pkg::flash_otp_key_rsp_t       flash_ctrl_otp_rsp;
  lc_ctrl_pkg::lc_tx_t       flash_ctrl_rma_req;
  lc_ctrl_pkg::lc_tx_t       flash_ctrl_rma_ack;
  lc_ctrl_pkg::lc_flash_rma_seed_t       flash_ctrl_rma_seed;
  sram_ctrl_pkg::sram_scr_req_t       sram_ctrl_main_sram_scr_req;
  sram_ctrl_pkg::sram_scr_rsp_t       sram_ctrl_main_sram_scr_rsp;
  sram_ctrl_pkg::sram_scr_req_t       sram_ctrl_ret_sram_scr_req;
  sram_ctrl_pkg::sram_scr_rsp_t       sram_ctrl_ret_sram_scr_rsp;
  otp_ctrl_pkg::sram_otp_key_req_t [1:0] otp_ctrl_sram_otp_key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t [1:0] otp_ctrl_sram_otp_key_rsp;
  pwrmgr_pkg::pwr_flash_req_t       pwrmgr_pwr_flash_req;
  pwrmgr_pkg::pwr_flash_rsp_t       pwrmgr_pwr_flash_rsp;
  pwrmgr_pkg::pwr_rst_req_t       pwrmgr_pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t       pwrmgr_pwr_rst_rsp;
  pwrmgr_pkg::pwr_clk_req_t       pwrmgr_pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t       pwrmgr_pwr_clk_rsp;
  pwrmgr_pkg::pwr_otp_req_t       pwrmgr_pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_pwr_otp_rsp;
  pwrmgr_pkg::pwr_lc_req_t       pwrmgr_pwr_lc_req;
  pwrmgr_pkg::pwr_lc_rsp_t       pwrmgr_pwr_lc_rsp;
  rv_core_ibex_pkg::crashdump_t       rv_core_ibex_crashdump;
  otp_ctrl_pkg::otp_keymgr_key_t       otp_ctrl_otp_keymgr_key;
  keymgr_pkg::hw_key_req_t       keymgr_kmac_key;
  keymgr_pkg::kmac_data_req_t       keymgr_kmac_data_req;
  keymgr_pkg::kmac_data_rsp_t       keymgr_kmac_data_rsp;
  logic [3:0] clkmgr_idle;
  otp_ctrl_pkg::otp_lc_data_t       otp_ctrl_otp_lc_data;
  otp_ctrl_pkg::lc_otp_program_req_t       lc_ctrl_lc_otp_program_req;
  otp_ctrl_pkg::lc_otp_program_rsp_t       lc_ctrl_lc_otp_program_rsp;
  otp_ctrl_pkg::lc_otp_token_req_t       lc_ctrl_lc_otp_token_req;
  otp_ctrl_pkg::lc_otp_token_rsp_t       lc_ctrl_lc_otp_token_rsp;
  otp_ctrl_part_pkg::otp_hw_cfg_t       otp_ctrl_otp_hw_cfg;
  lc_ctrl_pkg::lc_keymgr_div_t       lc_ctrl_lc_keymgr_div;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_nvm_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_cpu_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_check_byp_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_ack;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_creator_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_owner_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_iso_part_sw_rd_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_iso_part_sw_wr_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_seed_hw_rd_en;
  logic       pwrmgr_wakeups;
  logic       pwrmgr_rstreqs;
  tlul_pkg::tl_h2d_t       rom_tl_req;
  tlul_pkg::tl_d2h_t       rom_tl_rsp;
  tlul_pkg::tl_h2d_t       ram_main_tl_req;
  tlul_pkg::tl_d2h_t       ram_main_tl_rsp;
  tlul_pkg::tl_h2d_t       eflash_tl_req;
  tlul_pkg::tl_d2h_t       eflash_tl_rsp;
  tlul_pkg::tl_h2d_t       main_tl_peri_req;
  tlul_pkg::tl_d2h_t       main_tl_peri_rsp;
  tlul_pkg::tl_h2d_t       flash_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       flash_ctrl_tl_rsp;
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
  tlul_pkg::tl_h2d_t       pinmux_tl_req;
  tlul_pkg::tl_d2h_t       pinmux_tl_rsp;
  tlul_pkg::tl_h2d_t       padctrl_tl_req;
  tlul_pkg::tl_d2h_t       padctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       otbn_tl_req;
  tlul_pkg::tl_d2h_t       otbn_tl_rsp;
  tlul_pkg::tl_h2d_t       keymgr_tl_req;
  tlul_pkg::tl_d2h_t       keymgr_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_main_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_main_tl_rsp;
  tlul_pkg::tl_h2d_t       uart_tl_req;
  tlul_pkg::tl_d2h_t       uart_tl_rsp;
  tlul_pkg::tl_h2d_t       gpio_tl_req;
  tlul_pkg::tl_d2h_t       gpio_tl_rsp;
  tlul_pkg::tl_h2d_t       spi_device_tl_req;
  tlul_pkg::tl_d2h_t       spi_device_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_timer_tl_req;
  tlul_pkg::tl_d2h_t       rv_timer_tl_rsp;
  tlul_pkg::tl_h2d_t       usbdev_tl_req;
  tlul_pkg::tl_d2h_t       usbdev_tl_rsp;
  tlul_pkg::tl_h2d_t       pwrmgr_tl_req;
  tlul_pkg::tl_d2h_t       pwrmgr_tl_rsp;
  tlul_pkg::tl_h2d_t       rstmgr_tl_req;
  tlul_pkg::tl_d2h_t       rstmgr_tl_rsp;
  tlul_pkg::tl_h2d_t       clkmgr_tl_req;
  tlul_pkg::tl_d2h_t       clkmgr_tl_rsp;
  tlul_pkg::tl_h2d_t       ram_ret_tl_req;
  tlul_pkg::tl_d2h_t       ram_ret_tl_rsp;
  tlul_pkg::tl_h2d_t       otp_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       otp_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       lc_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       lc_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       sensor_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       sensor_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       alert_handler_tl_req;
  tlul_pkg::tl_d2h_t       alert_handler_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_tl_rsp;
  tlul_pkg::tl_h2d_t       nmi_gen_tl_req;
  tlul_pkg::tl_d2h_t       nmi_gen_tl_rsp;
  rstmgr_pkg::rstmgr_out_t       rstmgr_resets;
  rstmgr_pkg::rstmgr_cpu_t       rstmgr_cpu;
  pwrmgr_pkg::pwr_cpu_t       pwrmgr_pwr_cpu;
  clkmgr_pkg::clkmgr_out_t       clkmgr_clocks;
  tlul_pkg::tl_h2d_t       main_tl_corei_req;
  tlul_pkg::tl_d2h_t       main_tl_corei_rsp;
  tlul_pkg::tl_h2d_t       main_tl_cored_req;
  tlul_pkg::tl_d2h_t       main_tl_cored_rsp;
  tlul_pkg::tl_h2d_t       main_tl_dm_sba_req;
  tlul_pkg::tl_d2h_t       main_tl_dm_sba_rsp;
  tlul_pkg::tl_h2d_t       main_tl_debug_mem_req;
  tlul_pkg::tl_d2h_t       main_tl_debug_mem_rsp;


  // Unused reset signals
  logic unused_d0_rst_por_aon;
  logic unused_d0_rst_por;
  logic unused_d0_rst_por_io;
  logic unused_d0_rst_por_io_div2;
  logic unused_d0_rst_por_io_div4;
  logic unused_d0_rst_por_usb;
  logic unused_daon_rst_lc;
  logic unused_daon_rst_lc_io_div4;
  logic unused_d0_rst_sys_aon;
  logic unused_daon_rst_spi_device;
  logic unused_d0_rst_usb;
  assign unused_d0_rst_por_aon = rstmgr_resets.rst_por_aon_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por = rstmgr_resets.rst_por_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_io = rstmgr_resets.rst_por_io_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_io_div2 = rstmgr_resets.rst_por_io_div2_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_io_div4 = rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::Domain0Sel];
  assign unused_d0_rst_por_usb = rstmgr_resets.rst_por_usb_n[rstmgr_pkg::Domain0Sel];
  assign unused_daon_rst_lc = rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainAonSel];
  assign unused_daon_rst_lc_io_div4 = rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel];
  assign unused_d0_rst_sys_aon = rstmgr_resets.rst_sys_aon_n[rstmgr_pkg::Domain0Sel];
  assign unused_daon_rst_spi_device = rstmgr_resets.rst_spi_device_n[rstmgr_pkg::DomainAonSel];
  assign unused_d0_rst_usb = rstmgr_resets.rst_usb_n[rstmgr_pkg::Domain0Sel];

  // Non-debug module reset == reset for everything except for the debug module
  logic ndmreset_req;

  // debug request from rv_dm to core
  logic debug_req;

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
    .SecureIbex               (0),
    .DmHaltAddr               (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr          (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress),
    .PipeLine                 (IbexPipeLine)
  ) u_rv_core_ibex (
    // clock and reset
    .clk_i                (clkmgr_clocks.clk_proc_main),
    .rst_ni               (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .clk_esc_i            (clkmgr_clocks.clk_io_div4_timers),
    .rst_esc_ni           (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .test_en_i            (1'b0),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_ROM),
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
    .debug_req_i          (debug_req),
    // crash dump interface
    .crash_dump_o         (rv_core_ibex_crashdump),
    // CPU control signals
    .fetch_enable_i       (1'b1),
    .core_sleep_o         (pwrmgr_pwr_cpu.core_sleeping)
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  // TODO: this will be routed to the pinmux for TAP selection
  // based on straps and LC control signals.
  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;
  logic unused_jtag_tdo_oe_o;

  assign jtag_req.tck    = jtag_tck_i;
  assign jtag_req.tms    = jtag_tms_i;
  assign jtag_req.trst_n = jtag_trst_ni;
  assign jtag_req.tdi    = jtag_tdi_i;
  assign jtag_tdo_o      = jtag_rsp.tdo;
  assign unused_jtag_tdo_oe_o = jtag_rsp.tdo_oe;

  rv_dm #(
    .NrHarts     (1),
    .IdcodeValue (JTAG_IDCODE)
  ) u_dm_top (
    .clk_i         (clkmgr_clocks.clk_proc_main),
    .rst_ni        (rstmgr_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .testmode_i    (1'b0),
    .ndmreset_o    (ndmreset_req),
    .dmactive_o    (),
    .debug_req_o   (debug_req),
    .unavailable_i (1'b0),

    // bus device with debug memory (for execution-based debug)
    .tl_d_i        (main_tl_debug_mem_req),
    .tl_d_o        (main_tl_debug_mem_rsp),

    // bus host (for system bus accesses, SBA)
    .tl_h_o        (main_tl_dm_sba_req),
    .tl_h_i        (main_tl_dm_sba_rsp),

    //JTAG
    .jtag_req_i    (jtag_req),
    .jtag_rsp_o    (jtag_rsp)
  );

  assign rstmgr_cpu.ndmreset_req = ndmreset_req;
  assign rstmgr_cpu.rst_cpu_n = rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel];

  // ROM device
  logic        rom_req;
  logic [11:0] rom_addr;
  logic [31:0] rom_rdata;
  logic        rom_rvalid;

  tlul_adapter_sram #(
    .SramAw(12),
    .SramDw(32),
    .Outstanding(2),
    .ErrOnWrite(1)
  ) u_tl_adapter_rom (
    .clk_i   (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),

    .tl_i     (rom_tl_req),
    .tl_o     (rom_tl_rsp),

    .req_o    (rom_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (),
    .addr_o   (rom_addr),
    .wdata_o  (),
    .wmask_o  (),
    .rdata_i  (rom_rdata),
    .rvalid_i (rom_rvalid),
    .rerror_i (2'b00)
  );

  prim_rom_adv #(
    .Width(32),
    .Depth(4096),
    .MemInitFile(BootRomInitFile)
  ) u_rom_rom (
    .clk_i   (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .req_i    (rom_req),
    .addr_i   (rom_addr),
    .rdata_o  (rom_rdata),
    .rvalid_o (rom_rvalid),
    .cfg_i    ('0) // tied off for now
  );

  // sram device
  logic        ram_main_req;
  logic        ram_main_gnt;
  logic        ram_main_we;
  logic [13:0] ram_main_addr;
  logic [31:0] ram_main_wdata;
  logic [31:0] ram_main_wmask;
  logic [31:0] ram_main_rdata;
  logic        ram_main_rvalid;
  logic [1:0]  ram_main_rerror;

  tlul_adapter_sram #(
    .SramAw(14),
    .SramDw(32),
    .Outstanding(2)
  ) u_tl_adapter_ram_main (
    .clk_i   (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .tl_i     (ram_main_tl_req),
    .tl_o     (ram_main_tl_rsp),

    .req_o    (ram_main_req),
    .gnt_i    (ram_main_gnt),
    .we_o     (ram_main_we),
    .addr_o   (ram_main_addr),
    .wdata_o  (ram_main_wdata),
    .wmask_o  (ram_main_wmask),
    .rdata_i  (ram_main_rdata),
    .rvalid_i (ram_main_rvalid),
    .rerror_i (ram_main_rerror)
  );

  prim_ram_1p_scr #(
    .Width(32),
    .Depth(16384),
    .CfgWidth(8)
  ) u_ram1p_ram_main (
    .clk_i   (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),

    .key_valid_i ( sram_ctrl_main_sram_scr_req.valid ),
    .key_i       ( sram_ctrl_main_sram_scr_req.key   ),
    .nonce_i     ( sram_ctrl_main_sram_scr_req.nonce ),

    .req_i    (ram_main_req),
    .gnt_o    (ram_main_gnt),
    .write_i  (ram_main_we),
    .addr_i   (ram_main_addr),
    .wdata_i  (ram_main_wdata),
    .wmask_i  (ram_main_wmask),
    .rdata_o  (ram_main_rdata),
    .rvalid_o (ram_main_rvalid),
    .rerror_o (ram_main_rerror),
    .raddr_o  ( sram_ctrl_main_sram_scr_rsp.raddr ),
    .cfg_i    ( '0 )
  );

  assign sram_ctrl_main_sram_scr_rsp.rerror = ram_main_rerror;

  // sram device
  logic        ram_ret_req;
  logic        ram_ret_gnt;
  logic        ram_ret_we;
  logic [9:0] ram_ret_addr;
  logic [31:0] ram_ret_wdata;
  logic [31:0] ram_ret_wmask;
  logic [31:0] ram_ret_rdata;
  logic        ram_ret_rvalid;
  logic [1:0]  ram_ret_rerror;

  tlul_adapter_sram #(
    .SramAw(10),
    .SramDw(32),
    .Outstanding(2)
  ) u_tl_adapter_ram_ret (
    .clk_i   (clkmgr_clocks.clk_io_div4_infra),
    .rst_ni   (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .tl_i     (ram_ret_tl_req),
    .tl_o     (ram_ret_tl_rsp),

    .req_o    (ram_ret_req),
    .gnt_i    (ram_ret_gnt),
    .we_o     (ram_ret_we),
    .addr_o   (ram_ret_addr),
    .wdata_o  (ram_ret_wdata),
    .wmask_o  (ram_ret_wmask),
    .rdata_i  (ram_ret_rdata),
    .rvalid_i (ram_ret_rvalid),
    .rerror_i (ram_ret_rerror)
  );

  prim_ram_1p_scr #(
    .Width(32),
    .Depth(1024),
    .CfgWidth(8)
  ) u_ram1p_ram_ret (
    .clk_i   (clkmgr_clocks.clk_io_div4_infra),
    .rst_ni   (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),

    .key_valid_i ( sram_ctrl_ret_sram_scr_req.valid ),
    .key_i       ( sram_ctrl_ret_sram_scr_req.key   ),
    .nonce_i     ( sram_ctrl_ret_sram_scr_req.nonce ),

    .req_i    (ram_ret_req),
    .gnt_o    (ram_ret_gnt),
    .write_i  (ram_ret_we),
    .addr_i   (ram_ret_addr),
    .wdata_i  (ram_ret_wdata),
    .wmask_i  (ram_ret_wmask),
    .rdata_o  (ram_ret_rdata),
    .rvalid_o (ram_ret_rvalid),
    .rerror_o (ram_ret_rerror),
    .raddr_o  ( sram_ctrl_ret_sram_scr_rsp.raddr ),
    .cfg_i    ( '0 )
  );

  assign sram_ctrl_ret_sram_scr_rsp.rerror = ram_ret_rerror;


  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic flash_host_rderr;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;

  tlul_adapter_sram #(
    .SramAw(flash_ctrl_pkg::BusAddrW),
    .SramDw(flash_ctrl_pkg::BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1)
  ) u_tl_adapter_eflash (
    .clk_i   (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),

    .tl_i     (eflash_tl_req),
    .tl_o     (eflash_tl_rsp),

    .req_o    (flash_host_req),
    .gnt_i    (flash_host_req_rdy),
    .we_o     (),
    .addr_o   (flash_host_addr),
    .wdata_o  (),
    .wmask_o  (),
    .rdata_i  (flash_host_rdata),
    .rvalid_i (flash_host_req_done),
    .rerror_i ({flash_host_rderr,1'b0})
  );

  flash_phy u_flash_eflash (
    .clk_i   (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .host_req_i        (flash_host_req),
    .host_addr_i       (flash_host_addr),
    .host_req_rdy_o    (flash_host_req_rdy),
    .host_req_done_o   (flash_host_req_done),
    .host_rderr_o      (flash_host_rderr),
    .host_rdata_o      (flash_host_rdata),
    .flash_ctrl_i      (flash_ctrl_flash_req),
    .flash_ctrl_o      (flash_ctrl_flash_rsp),
    .lc_nvm_debug_en_i (lc_ctrl_lc_nvm_debug_en),
    .jtag_req_i        ('0),
    .jtag_rsp_o        (),
    .flash_bist_enable_i,
    .flash_power_down_h_i,
    .flash_power_ready_h_i,
    .flash_test_mode_a_i,
    .flash_test_voltage_h_i,
    .scanmode_i,
    .scan_rst_ni
  );



  uart u_uart (

      // Input
      .cio_rx_i    (cio_uart_rx_p2d),

      // Output
      .cio_tx_o    (cio_uart_tx_d2p),
      .cio_tx_en_o (cio_uart_tx_en_d2p),

      // Interrupt
      .intr_tx_watermark_o  (intr_uart_tx_watermark),
      .intr_rx_watermark_o  (intr_uart_rx_watermark),
      .intr_tx_empty_o      (intr_uart_tx_empty),
      .intr_rx_overflow_o   (intr_uart_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart_rx_break_err),
      .intr_rx_timeout_o    (intr_uart_rx_timeout),
      .intr_rx_parity_err_o (intr_uart_rx_parity_err),

      // Inter-module signals
      .tl_i(uart_tl_req),
      .tl_o(uart_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  gpio u_gpio (

      // Input
      .cio_gpio_i    (cio_gpio_gpio_p2d),

      // Output
      .cio_gpio_o    (cio_gpio_gpio_d2p),
      .cio_gpio_en_o (cio_gpio_gpio_en_d2p),

      // Interrupt
      .intr_gpio_o (intr_gpio_gpio),

      // Inter-module signals
      .tl_i(gpio_tl_req),
      .tl_o(gpio_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  spi_device u_spi_device (

      // Input
      .cio_sck_i    (cio_spi_device_sck_p2d),
      .cio_csb_i    (cio_spi_device_csb_p2d),
      .cio_sdi_i    (cio_spi_device_sdi_p2d),

      // Output
      .cio_sdo_o    (cio_spi_device_sdo_d2p),
      .cio_sdo_en_o (cio_spi_device_sdo_en_d2p),

      // Interrupt
      .intr_rxf_o         (intr_spi_device_rxf),
      .intr_rxlvl_o       (intr_spi_device_rxlvl),
      .intr_txlvl_o       (intr_spi_device_txlvl),
      .intr_rxerr_o       (intr_spi_device_rxerr),
      .intr_rxoverflow_o  (intr_spi_device_rxoverflow),
      .intr_txunderflow_o (intr_spi_device_txunderflow),

      // Inter-module signals
      .tl_i(spi_device_tl_req),
      .tl_o(spi_device_tl_rsp),
      .scanmode_i   (scanmode_i),
      .clk_i (clkmgr_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_resets.rst_spi_device_n[rstmgr_pkg::Domain0Sel])
  );

  rv_timer u_rv_timer (

      // Interrupt
      .intr_timer_expired_0_0_o (intr_rv_timer_timer_expired_0_0),

      // Inter-module signals
      .tl_i(rv_timer_tl_req),
      .tl_o(rv_timer_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_timers),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  sensor_ctrl u_sensor_ctrl (

      // [0]: as
      // [1]: cg
      // [2]: gd
      // [3]: ts_hi
      // [4]: ts_lo
      // [5]: ls
      // [6]: ot
      .alert_tx_o  ( alert_tx[6:0] ),
      .alert_rx_i  ( alert_rx[6:0] ),

      // Inter-module signals
      .ast_alert_i(sensor_ctrl_ast_alert_req_i),
      .ast_alert_o(sensor_ctrl_ast_alert_rsp_o),
      .ast_status_i(sensor_ctrl_ast_status_i),
      .tl_i(sensor_ctrl_tl_req),
      .tl_o(sensor_ctrl_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel])
  );

  otp_ctrl #(
    .RndCnstLfsrSeed(RndCnstOtpCtrlLfsrSeed),
    .RndCnstLfsrPerm(RndCnstOtpCtrlLfsrPerm)
  ) u_otp_ctrl (

      // Interrupt
      .intr_otp_operation_done_o (intr_otp_ctrl_otp_operation_done),
      .intr_otp_error_o          (intr_otp_ctrl_otp_error),

      // [7]: fatal_macro_error
      // [8]: fatal_check_error
      .alert_tx_o  ( alert_tx[8:7] ),
      .alert_rx_i  ( alert_rx[8:7] ),

      // Inter-module signals
      .otp_ast_pwr_seq_o(otp_ctrl_otp_ast_pwr_seq_o),
      .otp_ast_pwr_seq_h_i(otp_ctrl_otp_ast_pwr_seq_h_i),
      .edn_o(),
      .edn_i(edn_pkg::EDN_RSP_DEFAULT),
      .pwr_otp_i(pwrmgr_pwr_otp_req),
      .pwr_otp_o(pwrmgr_pwr_otp_rsp),
      .lc_otp_program_i(lc_ctrl_lc_otp_program_req),
      .lc_otp_program_o(lc_ctrl_lc_otp_program_rsp),
      .lc_otp_token_i(lc_ctrl_lc_otp_token_req),
      .lc_otp_token_o(lc_ctrl_lc_otp_token_rsp),
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
      .otbn_otp_key_i('0),
      .otbn_otp_key_o(),
      .otp_hw_cfg_o(otp_ctrl_otp_hw_cfg),
      .tl_i(otp_ctrl_tl_req),
      .tl_o(otp_ctrl_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_timers),
      .clk_edn_i (clkmgr_clocks.clk_main_timers),
      .rst_ni (rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  lc_ctrl #(
    .RndCnstLcKeymgrDivInvalid(RndCnstLcCtrlLcKeymgrDivInvalid),
    .RndCnstLcKeymgrDivTestDevRma(RndCnstLcCtrlLcKeymgrDivTestDevRma),
    .RndCnstLcKeymgrDivProduction(RndCnstLcCtrlLcKeymgrDivProduction)
  ) u_lc_ctrl (

      // [9]: fatal_prog_error
      // [10]: fatal_state_error
      .alert_tx_o  ( alert_tx[10:9] ),
      .alert_rx_i  ( alert_rx[10:9] ),

      // Inter-module signals
      .jtag_i(jtag_pkg::JTAG_REQ_DEFAULT),
      .jtag_o(),
      .esc_wipe_secrets_tx_i(alert_handler_esc_tx[1]),
      .esc_wipe_secrets_rx_o(alert_handler_esc_rx[1]),
      .esc_scrap_state_tx_i(alert_handler_esc_tx[2]),
      .esc_scrap_state_rx_o(alert_handler_esc_rx[2]),
      .pwr_lc_i(pwrmgr_pwr_lc_req),
      .pwr_lc_o(pwrmgr_pwr_lc_rsp),
      .otp_lc_data_i(otp_ctrl_otp_lc_data),
      .lc_otp_program_o(lc_ctrl_lc_otp_program_req),
      .lc_otp_program_i(lc_ctrl_lc_otp_program_rsp),
      .lc_otp_token_o(lc_ctrl_lc_otp_token_req),
      .lc_otp_token_i(lc_ctrl_lc_otp_token_rsp),
      .lc_dft_en_o(lc_ctrl_lc_dft_en),
      .lc_nvm_debug_en_o(lc_ctrl_lc_nvm_debug_en),
      .lc_hw_debug_en_o(lc_ctrl_lc_hw_debug_en),
      .lc_cpu_en_o(lc_ctrl_lc_cpu_en),
      .lc_keymgr_en_o(),
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
      .otp_hw_cfg_i(otp_ctrl_otp_hw_cfg),
      .tl_i(lc_ctrl_tl_req),
      .tl_o(lc_ctrl_tl_rsp),
      .scanmode_i   (scanmode_i),
      .clk_i (clkmgr_clocks.clk_io_div4_timers),
      .rst_ni (rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
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
      .entropy_i( 1'b0),
      .esc_rx_i(alert_handler_esc_rx),
      .esc_tx_o(alert_handler_esc_tx),
      .tl_i(alert_handler_tl_req),
      .tl_o(alert_handler_tl_rsp),
      // alert signals
      .alert_rx_o  ( alert_rx ),
      .alert_tx_i  ( alert_tx ),
      .clk_i (clkmgr_clocks.clk_io_div4_timers),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  nmi_gen u_nmi_gen (

      // Interrupt
      .intr_esc0_o (intr_nmi_gen_esc0),
      .intr_esc1_o (intr_nmi_gen_esc1),
      .intr_esc2_o (intr_nmi_gen_esc2),

      // Inter-module signals
      .nmi_rst_req_o(pwrmgr_rstreqs),
      .esc_tx_i('{3{prim_esc_pkg::ESC_TX_DEFAULT}}),
      .esc_rx_o(),
      .tl_i(nmi_gen_tl_req),
      .tl_o(nmi_gen_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_timers),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  pwrmgr u_pwrmgr (

      // Interrupt
      .intr_wakeup_o (intr_pwrmgr_wakeup),

      // Inter-module signals
      .pwr_ast_o(pwrmgr_pwr_ast_req_o),
      .pwr_ast_i(pwrmgr_pwr_ast_rsp_i),
      .pwr_rst_o(pwrmgr_pwr_rst_req),
      .pwr_rst_i(pwrmgr_pwr_rst_rsp),
      .pwr_clk_o(pwrmgr_pwr_clk_req),
      .pwr_clk_i(pwrmgr_pwr_clk_rsp),
      .pwr_otp_o(pwrmgr_pwr_otp_req),
      .pwr_otp_i(pwrmgr_pwr_otp_rsp),
      .pwr_lc_o(pwrmgr_pwr_lc_req),
      .pwr_lc_i(pwrmgr_pwr_lc_rsp),
      .pwr_flash_o(pwrmgr_pwr_flash_req),
      .pwr_flash_i(pwrmgr_pwr_flash_rsp),
      .esc_rst_tx_i(alert_handler_esc_tx[3]),
      .esc_rst_rx_o(alert_handler_esc_rx[3]),
      .pwr_cpu_i(pwrmgr_pwr_cpu),
      .wakeups_i(pwrmgr_wakeups),
      .rstreqs_i(pwrmgr_rstreqs),
      .tl_i(pwrmgr_tl_req),
      .tl_o(pwrmgr_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_powerup),
      .clk_slow_i (clkmgr_clocks.clk_aon_powerup),
      .rst_ni (rstmgr_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
      .rst_slow_ni (rstmgr_resets.rst_por_aon_n[rstmgr_pkg::DomainAonSel])
  );

  rstmgr u_rstmgr (

      // Inter-module signals
      .pwr_i(pwrmgr_pwr_rst_req),
      .pwr_o(pwrmgr_pwr_rst_rsp),
      .resets_o(rstmgr_resets),
      .ast_i(rstmgr_ast_i),
      .cpu_i(rstmgr_cpu),
      .alert_dump_i(alert_handler_crashdump),
      .cpu_dump_i(rv_core_ibex_crashdump),
      .resets_ast_o(rsts_ast_o),
      .tl_i(rstmgr_tl_req),
      .tl_o(rstmgr_tl_rsp),
      .scanmode_i   (scanmode_i),
      .scan_rst_ni  (scan_rst_ni),
      .clk_i (clkmgr_clocks.clk_io_div4_powerup),
      .clk_aon_i (clkmgr_clocks.clk_aon_powerup),
      .clk_main_i (clkmgr_clocks.clk_main_powerup),
      .clk_io_i (clkmgr_clocks.clk_io_powerup),
      .clk_usb_i (clkmgr_clocks.clk_usb_powerup),
      .clk_io_div2_i (clkmgr_clocks.clk_io_div2_powerup),
      .clk_io_div4_i (clkmgr_clocks.clk_io_div4_powerup),
      .rst_ni (rst_ni)
  );

  clkmgr u_clkmgr (

      // Inter-module signals
      .clocks_o(clkmgr_clocks),
      .ast_clk_bypass_ack_i(lc_ctrl_pkg::LC_TX_DEFAULT),
      .lc_clk_bypass_ack_o(lc_ctrl_lc_clk_byp_ack),
      .clk_main_i(clk_main_i),
      .clk_io_i(clk_io_i),
      .clk_usb_i(clk_usb_i),
      .clk_aon_i(clk_aon_i),
      .clocks_ast_o(clks_ast_o),
      .pwr_i(pwrmgr_pwr_clk_req),
      .pwr_o(pwrmgr_pwr_clk_rsp),
      .idle_i(clkmgr_idle),
      .tl_i(clkmgr_tl_req),
      .tl_o(clkmgr_tl_rsp),
      .scanmode_i   (scanmode_i),
      .clk_i (clkmgr_clocks.clk_io_div4_powerup),
      .rst_ni (rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_main_ni (rstmgr_resets.rst_por_n[rstmgr_pkg::DomainAonSel]),
      .rst_io_ni (rstmgr_resets.rst_por_io_n[rstmgr_pkg::DomainAonSel]),
      .rst_usb_ni (rstmgr_resets.rst_por_usb_n[rstmgr_pkg::DomainAonSel]),
      .rst_io_div2_ni (rstmgr_resets.rst_por_io_div2_n[rstmgr_pkg::DomainAonSel]),
      .rst_io_div4_ni (rstmgr_resets.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel])
  );

  pinmux u_pinmux (

      // Inter-module signals
      .lc_pinmux_strap_i('0),
      .lc_pinmux_strap_o(),
      .dft_strap_test_o(),
      .io_pok_i({pinmux_pkg::NIOPokSignals{1'b1}}),
      .sleep_en_i(1'b0),
      .aon_wkup_req_o(pwrmgr_wakeups),
      .tl_i(pinmux_tl_req),
      .tl_o(pinmux_tl_rsp),

      .periph_to_mio_i      (mio_d2p    ),
      .periph_to_mio_oe_i   (mio_d2p_en ),
      .mio_to_periph_o      (mio_p2d    ),

      .mio_out_o,
      .mio_oe_o,
      .mio_in_i,

      .periph_to_dio_i      (dio_d2p    ),
      .periph_to_dio_oe_i   (dio_d2p_en ),
      .dio_to_periph_o      (dio_p2d    ),

      .dio_out_o,
      .dio_oe_o,
      .dio_in_i,
      .clk_i (clkmgr_clocks.clk_main_secure),
      .clk_aon_i (clkmgr_clocks.clk_aon_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::DomainAonSel]),
      .rst_aon_ni (rstmgr_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel])
  );

  padctrl u_padctrl (

      // Inter-module signals
      .tl_i(padctrl_tl_req),
      .tl_o(padctrl_tl_rsp),

      .mio_attr_o,
      .dio_attr_o,
      .clk_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::DomainAonSel])
  );

  usbdev u_usbdev (

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

      // Inter-module signals
      .usb_ref_val_o(usbdev_usb_ref_val_o),
      .usb_ref_pulse_o(usbdev_usb_ref_pulse_o),
      .tl_i(usbdev_tl_req),
      .tl_o(usbdev_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_peri),
      .clk_usb_48mhz_i (clkmgr_clocks.clk_usb_peri),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_usb_48mhz_ni (rstmgr_resets.rst_usb_n[rstmgr_pkg::DomainAonSel])
  );

  sram_ctrl #(
    .RndCnstSramKey(RndCnstSramCtrlRetSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlRetSramNonce)
  ) u_sram_ctrl_ret (

      // [11]: fatal_parity_error
      .alert_tx_o  ( alert_tx[11:11] ),
      .alert_rx_i  ( alert_rx[11:11] ),

      // Inter-module signals
      .sram_otp_key_o(otp_ctrl_sram_otp_key_req[1]),
      .sram_otp_key_i(otp_ctrl_sram_otp_key_rsp[1]),
      .sram_scr_o(sram_ctrl_ret_sram_scr_req),
      .sram_scr_i(sram_ctrl_ret_sram_scr_rsp),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .tl_i(sram_ctrl_ret_tl_req),
      .tl_o(sram_ctrl_ret_tl_rsp),
      .clk_i (clkmgr_clocks.clk_io_div4_peri),
      .clk_otp_i (clkmgr_clocks.clk_io_div4_peri),
      .rst_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),
      .rst_otp_ni (rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel])
  );

  flash_ctrl #(
    .RndCnstAddrKey(RndCnstFlashCtrlAddrKey),
    .RndCnstDataKey(RndCnstFlashCtrlDataKey),
    .RndCnstLfsrSeed(RndCnstFlashCtrlLfsrSeed),
    .RndCnstLfsrPerm(RndCnstFlashCtrlLfsrPerm)
  ) u_flash_ctrl (

      // Interrupt
      .intr_prog_empty_o (intr_flash_ctrl_prog_empty),
      .intr_prog_lvl_o   (intr_flash_ctrl_prog_lvl),
      .intr_rd_full_o    (intr_flash_ctrl_rd_full),
      .intr_rd_lvl_o     (intr_flash_ctrl_rd_lvl),
      .intr_op_done_o    (intr_flash_ctrl_op_done),
      .intr_op_error_o   (intr_flash_ctrl_op_error),

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
      .rma_req_i(flash_ctrl_rma_req),
      .rma_ack_o(flash_ctrl_rma_ack),
      .rma_seed_i(flash_ctrl_rma_seed),
      .pwrmgr_i(pwrmgr_pwr_flash_req),
      .pwrmgr_o(pwrmgr_pwr_flash_rsp),
      .keymgr_o(flash_ctrl_keymgr),
      .tl_i(flash_ctrl_tl_req),
      .tl_o(flash_ctrl_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_infra),
      .clk_otp_i (clkmgr_clocks.clk_io_div4_infra),
      .rst_ni (rstmgr_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
      .rst_otp_ni (rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  rv_plic u_rv_plic (

      // Inter-module signals
      .tl_i(rv_plic_tl_req),
      .tl_o(rv_plic_tl_rsp),

      .intr_src_i (intr_vector),
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  aes #(
    .AES192Enable(1'b1),
    .Masking(AesMasking),
    .SBoxImpl(AesSBoxImpl),
    .SecStartTriggerDelay(SecAesStartTriggerDelay),
    .SecAllowForcingMasks(SecAesAllowForcingMasks),
    .AlertAsyncOn({aes_reg_pkg::NumAlerts{1'b1}}),
    .RndCnstClearingLfsrSeed(aes_pkg::RndCnstClearingLfsrSeedDefault),
    .RndCnstClearingLfsrPerm(aes_pkg::RndCnstClearingLfsrPermDefault),
    .RndCnstMaskingLfsrSeed(aes_pkg::RndCnstMaskingLfsrSeedDefault),
    .RndCnstMskgChunkLfsrPerm(aes_pkg::RndCnstMskgChunkLfsrPermDefault)
  ) u_aes (

      // [12]: recov_ctrl_update_err
      // [13]: fatal_fault
      .alert_tx_o  ( alert_tx[13:12] ),
      .alert_rx_i  ( alert_rx[13:12] ),

      // Inter-module signals
      .idle_o(clkmgr_idle[0]),
      .tl_i(aes_tl_req),
      .tl_o(aes_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_aes),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  hmac u_hmac (

      // Interrupt
      .intr_hmac_done_o  (intr_hmac_hmac_done),
      .intr_fifo_empty_o (intr_hmac_fifo_empty),
      .intr_hmac_err_o   (intr_hmac_hmac_err),

      // Inter-module signals
      .idle_o(clkmgr_idle[1]),
      .tl_i(hmac_tl_req),
      .tl_o(hmac_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_hmac),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  kmac #(
    .EnMasking(KmacEnMasking),
    .ReuseShare(KmacReuseShare)
  ) u_kmac (

      // Interrupt
      .intr_kmac_done_o  (intr_kmac_kmac_done),
      .intr_fifo_empty_o (intr_kmac_fifo_empty),
      .intr_kmac_err_o   (intr_kmac_kmac_err),

      // Inter-module signals
      .keymgr_key_i(keymgr_kmac_key),
      .keymgr_kdf_i(keymgr_kmac_data_req),
      .keymgr_kdf_o(keymgr_kmac_data_rsp),
      .entropy_o(),
      .entropy_i(edn_pkg::EDN_RSP_DEFAULT),
      .idle_o(clkmgr_idle[2]),
      .tl_i(kmac_tl_req),
      .tl_o(kmac_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_kmac),
      .clk_edn_i (clkmgr_clocks.clk_main_kmac),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  keymgr #(
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
    .RndCnstNoneSeed(RndCnstKeymgrNoneSeed)
  ) u_keymgr (

      // Interrupt
      .intr_op_done_o (intr_keymgr_op_done),

      // [14]: fault_err
      // [15]: operation_err
      .alert_tx_o  ( alert_tx[15:14] ),
      .alert_rx_i  ( alert_rx[15:14] ),

      // Inter-module signals
      .edn_o(),
      .edn_i(edn_pkg::EDN_RSP_DEFAULT),
      .aes_key_o(),
      .hmac_key_o(),
      .kmac_key_o(keymgr_kmac_key),
      .kmac_data_o(keymgr_kmac_data_req),
      .kmac_data_i(keymgr_kmac_data_rsp),
      .otp_key_i(otp_ctrl_otp_keymgr_key),
      .otp_hw_cfg_i(otp_ctrl_otp_hw_cfg),
      .flash_i(flash_ctrl_keymgr),
      .lc_keymgr_en_i(lc_ctrl_pkg::On),
      .lc_keymgr_div_i(lc_ctrl_lc_keymgr_div),
      .tl_i(keymgr_tl_req),
      .tl_o(keymgr_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .clk_edn_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_edn_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  csrng #(
    .SBoxImpl(CsrngSBoxImpl)
  ) u_csrng (

      // Interrupt
      .intr_cs_cmd_req_done_o (intr_csrng_cs_cmd_req_done),
      .intr_cs_entropy_req_o  (intr_csrng_cs_entropy_req),
      .intr_cs_hw_inst_exc_o  (intr_csrng_cs_hw_inst_exc),
      .intr_cs_fifo_err_o     (intr_csrng_cs_fifo_err),

      // Inter-module signals
      .csrng_cmd_i(csrng_csrng_cmd_req),
      .csrng_cmd_o(csrng_csrng_cmd_rsp),
      .entropy_src_hw_if_o(csrng_entropy_src_hw_if_req),
      .entropy_src_hw_if_i(csrng_entropy_src_hw_if_rsp),
      .efuse_sw_app_enable_i('0),
      .lc_hw_debug_en_i(lc_ctrl_pkg::Off),
      .tl_i(csrng_tl_req),
      .tl_o(csrng_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  entropy_src u_entropy_src (

      // Interrupt
      .intr_es_entropy_valid_o      (intr_entropy_src_es_entropy_valid),
      .intr_es_health_test_failed_o (intr_entropy_src_es_health_test_failed),
      .intr_es_fifo_err_o           (intr_entropy_src_es_fifo_err),

      // [16]: recov_alert_count_met
      .alert_tx_o  ( alert_tx[16:16] ),
      .alert_rx_i  ( alert_rx[16:16] ),

      // Inter-module signals
      .entropy_src_hw_if_i(csrng_entropy_src_hw_if_req),
      .entropy_src_hw_if_o(csrng_entropy_src_hw_if_rsp),
      .entropy_src_rng_o(),
      .entropy_src_rng_i(entropy_src_pkg::ENTROPY_SRC_RNG_RSP_DEFAULT),
      .entropy_src_xht_o(),
      .entropy_src_xht_i(entropy_src_pkg::ENTROPY_SRC_XHT_RSP_DEFAULT),
      .efuse_es_sw_reg_en_i('0),
      .tl_i(entropy_src_tl_req),
      .tl_o(entropy_src_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  edn u_edn0 (

      // Interrupt
      .intr_edn_cmd_req_done_o (intr_edn0_edn_cmd_req_done),
      .intr_edn_fifo_err_o     (intr_edn0_edn_fifo_err),

      // Inter-module signals
      .csrng_cmd_o(csrng_csrng_cmd_req[0]),
      .csrng_cmd_i(csrng_csrng_cmd_rsp[0]),
      .edn_i(edn_pkg::EDN_REQ_DEFAULT),
      .edn_o(),
      .tl_i(edn0_tl_req),
      .tl_o(edn0_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  edn u_edn1 (

      // Interrupt
      .intr_edn_cmd_req_done_o (intr_edn1_edn_cmd_req_done),
      .intr_edn_fifo_err_o     (intr_edn1_edn_fifo_err),

      // Inter-module signals
      .csrng_cmd_o(csrng_csrng_cmd_req[1]),
      .csrng_cmd_i(csrng_csrng_cmd_rsp[1]),
      .edn_i(edn_pkg::EDN_REQ_DEFAULT),
      .edn_o(),
      .tl_i(edn1_tl_req),
      .tl_o(edn1_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  sram_ctrl #(
    .RndCnstSramKey(RndCnstSramCtrlMainSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlMainSramNonce)
  ) u_sram_ctrl_main (

      // [17]: fatal_parity_error
      .alert_tx_o  ( alert_tx[17:17] ),
      .alert_rx_i  ( alert_rx[17:17] ),

      // Inter-module signals
      .sram_otp_key_o(otp_ctrl_sram_otp_key_req[0]),
      .sram_otp_key_i(otp_ctrl_sram_otp_key_rsp[0]),
      .sram_scr_o(sram_ctrl_main_sram_scr_req),
      .sram_scr_i(sram_ctrl_main_sram_scr_rsp),
      .lc_escalate_en_i(lc_ctrl_lc_escalate_en),
      .tl_i(sram_ctrl_main_tl_req),
      .tl_o(sram_ctrl_main_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_secure),
      .clk_otp_i (clkmgr_clocks.clk_io_div4_secure),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
      .rst_otp_ni (rstmgr_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel])
  );

  otbn #(
    .RegFile(OtbnRegFile)
  ) u_otbn (

      // Interrupt
      .intr_done_o (intr_otbn_done),

      // [18]: fatal
      // [19]: recov
      .alert_tx_o  ( alert_tx[19:18] ),
      .alert_rx_i  ( alert_rx[19:18] ),

      // Inter-module signals
      .idle_o(clkmgr_idle[3]),
      .tl_i(otbn_tl_req),
      .tl_o(otbn_tl_rsp),
      .clk_i (clkmgr_clocks.clk_main_otbn),
      .rst_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel])
  );

  // interrupt assignments
  assign intr_vector = {
      intr_entropy_src_es_fifo_err,
      intr_entropy_src_es_health_test_failed,
      intr_entropy_src_es_entropy_valid,
      intr_edn1_edn_fifo_err,
      intr_edn1_edn_cmd_req_done,
      intr_edn0_edn_fifo_err,
      intr_edn0_edn_cmd_req_done,
      intr_csrng_cs_fifo_err,
      intr_csrng_cs_hw_inst_exc,
      intr_csrng_cs_entropy_req,
      intr_csrng_cs_cmd_req_done,
      intr_otp_ctrl_otp_error,
      intr_otp_ctrl_otp_operation_done,
      intr_kmac_kmac_err,
      intr_kmac_fifo_empty,
      intr_kmac_kmac_done,
      intr_keymgr_op_done,
      intr_otbn_done,
      intr_pwrmgr_wakeup,
      intr_usbdev_link_out_err,
      intr_usbdev_connected,
      intr_usbdev_frame,
      intr_usbdev_rx_bitstuff_err,
      intr_usbdev_rx_pid_err,
      intr_usbdev_rx_crc_err,
      intr_usbdev_link_in_err,
      intr_usbdev_av_overflow,
      intr_usbdev_rx_full,
      intr_usbdev_av_empty,
      intr_usbdev_link_resume,
      intr_usbdev_link_suspend,
      intr_usbdev_link_reset,
      intr_usbdev_host_lost,
      intr_usbdev_disconnected,
      intr_usbdev_pkt_sent,
      intr_usbdev_pkt_received,
      intr_nmi_gen_esc2,
      intr_nmi_gen_esc1,
      intr_nmi_gen_esc0,
      intr_alert_handler_classd,
      intr_alert_handler_classc,
      intr_alert_handler_classb,
      intr_alert_handler_classa,
      intr_hmac_hmac_err,
      intr_hmac_fifo_empty,
      intr_hmac_hmac_done,
      intr_flash_ctrl_op_error,
      intr_flash_ctrl_op_done,
      intr_flash_ctrl_rd_lvl,
      intr_flash_ctrl_rd_full,
      intr_flash_ctrl_prog_lvl,
      intr_flash_ctrl_prog_empty,
      intr_spi_device_txunderflow,
      intr_spi_device_rxoverflow,
      intr_spi_device_rxerr,
      intr_spi_device_txlvl,
      intr_spi_device_rxlvl,
      intr_spi_device_rxf,
      intr_uart_rx_parity_err,
      intr_uart_rx_timeout,
      intr_uart_rx_break_err,
      intr_uart_rx_frame_err,
      intr_uart_rx_overflow,
      intr_uart_tx_empty,
      intr_uart_rx_watermark,
      intr_uart_tx_watermark,
      intr_gpio_gpio,
      1'b 0 // For ID 0.
  };

  // TL-UL Crossbar
  xbar_main u_xbar_main (
    .clk_main_i (clkmgr_clocks.clk_main_infra),
    .clk_fixed_i (clkmgr_clocks.clk_io_div4_infra),
    .rst_main_ni (rstmgr_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_fixed_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),

    // port: tl_corei
    .tl_corei_i(main_tl_corei_req),
    .tl_corei_o(main_tl_corei_rsp),

    // port: tl_cored
    .tl_cored_i(main_tl_cored_req),
    .tl_cored_o(main_tl_cored_rsp),

    // port: tl_dm_sba
    .tl_dm_sba_i(main_tl_dm_sba_req),
    .tl_dm_sba_o(main_tl_dm_sba_rsp),

    // port: tl_rom
    .tl_rom_o(rom_tl_req),
    .tl_rom_i(rom_tl_rsp),

    // port: tl_debug_mem
    .tl_debug_mem_o(main_tl_debug_mem_req),
    .tl_debug_mem_i(main_tl_debug_mem_rsp),

    // port: tl_ram_main
    .tl_ram_main_o(ram_main_tl_req),
    .tl_ram_main_i(ram_main_tl_rsp),

    // port: tl_eflash
    .tl_eflash_o(eflash_tl_req),
    .tl_eflash_i(eflash_tl_rsp),

    // port: tl_peri
    .tl_peri_o(main_tl_peri_req),
    .tl_peri_i(main_tl_peri_rsp),

    // port: tl_flash_ctrl
    .tl_flash_ctrl_o(flash_ctrl_tl_req),
    .tl_flash_ctrl_i(flash_ctrl_tl_rsp),

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

    // port: tl_pinmux
    .tl_pinmux_o(pinmux_tl_req),
    .tl_pinmux_i(pinmux_tl_rsp),

    // port: tl_padctrl
    .tl_padctrl_o(padctrl_tl_req),
    .tl_padctrl_i(padctrl_tl_rsp),

    // port: tl_otbn
    .tl_otbn_o(otbn_tl_req),
    .tl_otbn_i(otbn_tl_rsp),

    // port: tl_keymgr
    .tl_keymgr_o(keymgr_tl_req),
    .tl_keymgr_i(keymgr_tl_rsp),

    // port: tl_sram_ctrl_main
    .tl_sram_ctrl_main_o(sram_ctrl_main_tl_req),
    .tl_sram_ctrl_main_i(sram_ctrl_main_tl_rsp),


    .scanmode_i
  );
  xbar_peri u_xbar_peri (
    .clk_peri_i (clkmgr_clocks.clk_io_div4_infra),
    .rst_peri_ni (rstmgr_resets.rst_sys_io_div4_n[rstmgr_pkg::Domain0Sel]),

    // port: tl_main
    .tl_main_i(main_tl_peri_req),
    .tl_main_o(main_tl_peri_rsp),

    // port: tl_uart
    .tl_uart_o(uart_tl_req),
    .tl_uart_i(uart_tl_rsp),

    // port: tl_gpio
    .tl_gpio_o(gpio_tl_req),
    .tl_gpio_i(gpio_tl_rsp),

    // port: tl_spi_device
    .tl_spi_device_o(spi_device_tl_req),
    .tl_spi_device_i(spi_device_tl_rsp),

    // port: tl_rv_timer
    .tl_rv_timer_o(rv_timer_tl_req),
    .tl_rv_timer_i(rv_timer_tl_rsp),

    // port: tl_usbdev
    .tl_usbdev_o(usbdev_tl_req),
    .tl_usbdev_i(usbdev_tl_rsp),

    // port: tl_pwrmgr
    .tl_pwrmgr_o(pwrmgr_tl_req),
    .tl_pwrmgr_i(pwrmgr_tl_rsp),

    // port: tl_rstmgr
    .tl_rstmgr_o(rstmgr_tl_req),
    .tl_rstmgr_i(rstmgr_tl_rsp),

    // port: tl_clkmgr
    .tl_clkmgr_o(clkmgr_tl_req),
    .tl_clkmgr_i(clkmgr_tl_rsp),

    // port: tl_ram_ret
    .tl_ram_ret_o(ram_ret_tl_req),
    .tl_ram_ret_i(ram_ret_tl_rsp),

    // port: tl_otp_ctrl
    .tl_otp_ctrl_o(otp_ctrl_tl_req),
    .tl_otp_ctrl_i(otp_ctrl_tl_rsp),

    // port: tl_lc_ctrl
    .tl_lc_ctrl_o(lc_ctrl_tl_req),
    .tl_lc_ctrl_i(lc_ctrl_tl_rsp),

    // port: tl_sensor_ctrl
    .tl_sensor_ctrl_o(sensor_ctrl_tl_req),
    .tl_sensor_ctrl_i(sensor_ctrl_tl_rsp),

    // port: tl_alert_handler
    .tl_alert_handler_o(alert_handler_tl_req),
    .tl_alert_handler_i(alert_handler_tl_rsp),

    // port: tl_sram_ctrl_ret
    .tl_sram_ctrl_ret_o(sram_ctrl_ret_tl_req),
    .tl_sram_ctrl_ret_i(sram_ctrl_ret_tl_rsp),

    // port: tl_nmi_gen
    .tl_nmi_gen_o(nmi_gen_tl_req),
    .tl_nmi_gen_i(nmi_gen_tl_rsp),

    // port: tl_ast_wrapper
    .tl_ast_wrapper_o(ast_tl_req_o),
    .tl_ast_wrapper_i(ast_tl_rsp_i),


    .scanmode_i
  );

  // Pinmux connections
  assign mio_d2p = {
    cio_gpio_gpio_d2p
  };
  assign mio_d2p_en = {
    cio_gpio_gpio_en_d2p
  };
  assign {
    cio_gpio_gpio_p2d
  } = mio_p2d;

  // Dedicated IO connections
  // Input-only DIOs have no d2p signals
  assign dio_d2p = {
    1'b0, // DIO14: cio_spi_device_sck
    1'b0, // DIO13: cio_spi_device_csb
    1'b0, // DIO12: cio_spi_device_sdi
    cio_spi_device_sdo_d2p, // DIO11
    1'b0, // DIO10: cio_uart_rx
    cio_uart_tx_d2p, // DIO9
    1'b0, // DIO8: cio_usbdev_sense
    cio_usbdev_se0_d2p, // DIO7
    cio_usbdev_dp_pullup_d2p, // DIO6
    cio_usbdev_dn_pullup_d2p, // DIO5
    cio_usbdev_tx_mode_se_d2p, // DIO4
    cio_usbdev_suspend_d2p, // DIO3
    cio_usbdev_d_d2p, // DIO2
    cio_usbdev_dp_d2p, // DIO1
    cio_usbdev_dn_d2p // DIO0
  };

  assign dio_d2p_en = {
    1'b0, // DIO14: cio_spi_device_sck
    1'b0, // DIO13: cio_spi_device_csb
    1'b0, // DIO12: cio_spi_device_sdi
    cio_spi_device_sdo_en_d2p, // DIO11
    1'b0, // DIO10: cio_uart_rx
    cio_uart_tx_en_d2p, // DIO9
    1'b0, // DIO8: cio_usbdev_sense
    cio_usbdev_se0_en_d2p, // DIO7
    cio_usbdev_dp_pullup_en_d2p, // DIO6
    cio_usbdev_dn_pullup_en_d2p, // DIO5
    cio_usbdev_tx_mode_se_en_d2p, // DIO4
    cio_usbdev_suspend_en_d2p, // DIO3
    cio_usbdev_d_en_d2p, // DIO2
    cio_usbdev_dp_en_d2p, // DIO1
    cio_usbdev_dn_en_d2p // DIO0
  };

  // Output-only DIOs have no p2d signal
  assign cio_spi_device_sck_p2d    = dio_p2d[14]; // DIO14
  assign cio_spi_device_csb_p2d    = dio_p2d[13]; // DIO13
  assign cio_spi_device_sdi_p2d    = dio_p2d[12]; // DIO12
  // DIO11: cio_spi_device_sdo
  assign cio_uart_rx_p2d           = dio_p2d[10]; // DIO10
  // DIO9: cio_uart_tx
  assign cio_usbdev_sense_p2d      = dio_p2d[8]; // DIO8
  // DIO7: cio_usbdev_se0
  // DIO6: cio_usbdev_dp_pullup
  // DIO5: cio_usbdev_dn_pullup
  // DIO4: cio_usbdev_tx_mode_se
  // DIO3: cio_usbdev_suspend
  assign cio_usbdev_d_p2d          = dio_p2d[2]; // DIO2
  assign cio_usbdev_dp_p2d         = dio_p2d[1]; // DIO1
  assign cio_usbdev_dn_p2d         = dio_p2d[0]; // DIO0

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_main_i, 0)

endmodule
