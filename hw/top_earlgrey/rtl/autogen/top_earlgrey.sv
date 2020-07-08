// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey #(
  parameter bit IbexPipeLine = 0
) (
  // Clock and Reset
  input               clk_i,
  input               rst_ni,

  // Fixed io clock
  input               clk_io_i,

  // USB clock
  input               clk_usb_i,

  // aon clock
  input               clk_aon_i,

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
  input        [28:0] dio_in_i,
  output logic [28:0] dio_out_o,
  output logic [28:0] dio_oe_o,

  // pad attributes to padring
  output logic[padctrl_reg_pkg::NMioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_o,
  output logic[padctrl_reg_pkg::NDioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_o,


  // Inter-module Signal External type
  output tlul_pkg::tl_h2d_t       sensor_ctrl_ast_host,
  input  tlul_pkg::tl_d2h_t       sensor_ctrl_ast_dev,
  input  ast_wrapper_pkg::ast_status_t       sensor_ctrl_ast_status,
  input  ast_wrapper_pkg::ast_alert_req_t       sensor_ctrl_ast_alert_req,
  output ast_wrapper_pkg::ast_alert_rsp_t       sensor_ctrl_ast_alert_rsp,
  output sensor_ctrl_pkg::ast_aux_t       sensor_ctrl_ast_aux,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_aon_pwr_ast_req,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_aon_pwr_ast_rsp,
  input  ast_wrapper_pkg::ast_rst_t       rstmgr_aon_ast,
  output logic       usbdev_aon_usb_ref_pulse,
  output logic       usbdev_aon_usb_ref_val,
  output entropy_src_pkg::entropy_src_rng_req_t       entropy_src_entropy_src_rng_req,
  input  entropy_src_pkg::entropy_src_rng_rsp_t       entropy_src_entropy_src_rng_rsp,

  input               scanmode_i  // 1 for Scan
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

  tl_h2d_t  tl_corei_h_h2d;
  tl_d2h_t  tl_corei_h_d2h;

  tl_h2d_t  tl_cored_h_h2d;
  tl_d2h_t  tl_cored_h_d2h;

  tl_h2d_t  tl_dm_sba_h_h2d;
  tl_d2h_t  tl_dm_sba_h_d2h;

  tl_h2d_t  tl_debug_mem_d_h2d;
  tl_d2h_t  tl_debug_mem_d_d2h;

  tl_h2d_t  tl_uart_d_h2d;
  tl_d2h_t  tl_uart_d_d2h;
  tl_h2d_t  tl_uart1_d_h2d;
  tl_d2h_t  tl_uart1_d_d2h;
  tl_h2d_t  tl_uart2_d_h2d;
  tl_d2h_t  tl_uart2_d_d2h;
  tl_h2d_t  tl_uart3_d_h2d;
  tl_d2h_t  tl_uart3_d_d2h;
  tl_h2d_t  tl_gpio_d_h2d;
  tl_d2h_t  tl_gpio_d_d2h;
  tl_h2d_t  tl_spi_device_d_h2d;
  tl_d2h_t  tl_spi_device_d_d2h;
  tl_h2d_t  tl_flash_ctrl_d_h2d;
  tl_d2h_t  tl_flash_ctrl_d_d2h;
  tl_h2d_t  tl_rv_timer_d_h2d;
  tl_d2h_t  tl_rv_timer_d_d2h;
  tl_h2d_t  tl_i2c0_d_h2d;
  tl_d2h_t  tl_i2c0_d_d2h;
  tl_h2d_t  tl_i2c1_d_h2d;
  tl_d2h_t  tl_i2c1_d_d2h;
  tl_h2d_t  tl_i2c2_d_h2d;
  tl_d2h_t  tl_i2c2_d_d2h;
  tl_h2d_t  tl_sensor_ctrl_d_h2d;
  tl_d2h_t  tl_sensor_ctrl_d_d2h;
  tl_h2d_t  tl_otp_ctrl_d_h2d;
  tl_d2h_t  tl_otp_ctrl_d_d2h;
  tl_h2d_t  tl_lifecycle_d_h2d;
  tl_d2h_t  tl_lifecycle_d_d2h;
  tl_h2d_t  tl_aes_d_h2d;
  tl_d2h_t  tl_aes_d_d2h;
  tl_h2d_t  tl_hmac_d_h2d;
  tl_d2h_t  tl_hmac_d_d2h;
  tl_h2d_t  tl_kmac_d_h2d;
  tl_d2h_t  tl_kmac_d_d2h;
  tl_h2d_t  tl_rv_plic_d_h2d;
  tl_d2h_t  tl_rv_plic_d_d2h;
  tl_h2d_t  tl_pinmux_aon_d_h2d;
  tl_d2h_t  tl_pinmux_aon_d_d2h;
  tl_h2d_t  tl_padctrl_aon_d_h2d;
  tl_d2h_t  tl_padctrl_aon_d_d2h;
  tl_h2d_t  tl_alert_handler_d_h2d;
  tl_d2h_t  tl_alert_handler_d_d2h;
  tl_h2d_t  tl_pwrmgr_aon_d_h2d;
  tl_d2h_t  tl_pwrmgr_aon_d_d2h;
  tl_h2d_t  tl_rstmgr_aon_d_h2d;
  tl_d2h_t  tl_rstmgr_aon_d_d2h;
  tl_h2d_t  tl_clkmgr_aon_d_h2d;
  tl_d2h_t  tl_clkmgr_aon_d_d2h;
  tl_h2d_t  tl_rbox_aon_d_h2d;
  tl_d2h_t  tl_rbox_aon_d_d2h;
  tl_h2d_t  tl_pwm_aon_d_h2d;
  tl_d2h_t  tl_pwm_aon_d_d2h;
  tl_h2d_t  tl_timer_aon_d_h2d;
  tl_d2h_t  tl_timer_aon_d_d2h;
  tl_h2d_t  tl_nmi_gen_d_h2d;
  tl_d2h_t  tl_nmi_gen_d_d2h;
  tl_h2d_t  tl_usbdev_aon_d_h2d;
  tl_d2h_t  tl_usbdev_aon_d_d2h;
  tl_h2d_t  tl_pattgen_d_h2d;
  tl_d2h_t  tl_pattgen_d_d2h;
  tl_h2d_t  tl_keymgr_d_h2d;
  tl_d2h_t  tl_keymgr_d_d2h;
  tl_h2d_t  tl_csrng_d_h2d;
  tl_d2h_t  tl_csrng_d_d2h;
  tl_h2d_t  tl_entropy_src_d_h2d;
  tl_d2h_t  tl_entropy_src_d_d2h;
  tl_h2d_t  tl_otbn_d_h2d;
  tl_d2h_t  tl_otbn_d_d2h;

  tl_h2d_t tl_rom_d_h2d;
  tl_d2h_t tl_rom_d_d2h;
  tl_h2d_t tl_ram_main_d_h2d;
  tl_d2h_t tl_ram_main_d_d2h;
  tl_h2d_t tl_ram_ret_aon_d_h2d;
  tl_d2h_t tl_ram_ret_aon_d_d2h;
  tl_h2d_t tl_eflash_d_h2d;
  tl_d2h_t tl_eflash_d_d2h;

  tl_h2d_t tl_main_peri_h2d;
  tl_d2h_t tl_main_peri_d2h;
  tl_h2d_t tl_main_aon_h2d;
  tl_d2h_t tl_main_aon_d2h;

  // Signals
  logic [40:0] mio_p2d;
  logic [40:0] mio_d2p;
  logic [40:0] mio_d2p_en;
  logic [28:0] dio_p2d;
  logic [28:0] dio_d2p;
  logic [28:0] dio_d2p_en;
  // uart
  logic        cio_uart_rx_p2d;
  logic        cio_uart_tx_d2p;
  logic        cio_uart_tx_en_d2p;
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
  logic        cio_spi_device_mosi_p2d;
  logic        cio_spi_device_miso_d2p;
  logic        cio_spi_device_miso_en_d2p;
  // flash_ctrl
  // rv_timer
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
  // sensor_ctrl
  // otp_ctrl
  // lifecycle
  // aes
  // hmac
  // kmac
  // rv_plic
  // pinmux_aon
  // padctrl_aon
  // alert_handler
  // pwrmgr_aon
  // rstmgr_aon
  // clkmgr_aon
  // rbox_aon
  logic        cio_rbox_aon_ac_present_p2d;
  logic        cio_rbox_aon_ec_entering_rw_p2d;
  logic        cio_rbox_aon_key0_in_p2d;
  logic        cio_rbox_aon_key1_in_p2d;
  logic        cio_rbox_aon_key2_in_p2d;
  logic        cio_rbox_aon_pwrb_in_p2d;
  logic        cio_rbox_aon_bat_en_d2p;
  logic        cio_rbox_aon_bat_en_en_d2p;
  logic        cio_rbox_aon_ec_in_rw_d2p;
  logic        cio_rbox_aon_ec_in_rw_en_d2p;
  logic        cio_rbox_aon_ec_rst_l_d2p;
  logic        cio_rbox_aon_ec_rst_l_en_d2p;
  logic        cio_rbox_aon_flash_wp_l_d2p;
  logic        cio_rbox_aon_flash_wp_l_en_d2p;
  logic        cio_rbox_aon_key0_out_d2p;
  logic        cio_rbox_aon_key0_out_en_d2p;
  logic        cio_rbox_aon_key1_out_d2p;
  logic        cio_rbox_aon_key1_out_en_d2p;
  logic        cio_rbox_aon_key2_out_d2p;
  logic        cio_rbox_aon_key2_out_en_d2p;
  logic        cio_rbox_aon_pwrb_out_d2p;
  logic        cio_rbox_aon_pwrb_out_en_d2p;
  // pwm_aon
  logic [8:0]  cio_pwm_aon_pwm_d2p;
  logic [8:0]  cio_pwm_aon_pwm_en_d2p;
  // timer_aon
  // nmi_gen
  // usbdev_aon
  logic        cio_usbdev_aon_sense_p2d;
  logic        cio_usbdev_aon_d_p2d;
  logic        cio_usbdev_aon_dp_p2d;
  logic        cio_usbdev_aon_dn_p2d;
  logic        cio_usbdev_aon_se0_d2p;
  logic        cio_usbdev_aon_se0_en_d2p;
  logic        cio_usbdev_aon_dp_pullup_d2p;
  logic        cio_usbdev_aon_dp_pullup_en_d2p;
  logic        cio_usbdev_aon_dn_pullup_d2p;
  logic        cio_usbdev_aon_dn_pullup_en_d2p;
  logic        cio_usbdev_aon_tx_mode_se_d2p;
  logic        cio_usbdev_aon_tx_mode_se_en_d2p;
  logic        cio_usbdev_aon_suspend_d2p;
  logic        cio_usbdev_aon_suspend_en_d2p;
  logic        cio_usbdev_aon_d_d2p;
  logic        cio_usbdev_aon_d_en_d2p;
  logic        cio_usbdev_aon_dp_d2p;
  logic        cio_usbdev_aon_dp_en_d2p;
  logic        cio_usbdev_aon_dn_d2p;
  logic        cio_usbdev_aon_dn_en_d2p;
  // pattgen
  logic        cio_pattgen_pda0_tx_d2p;
  logic        cio_pattgen_pda0_tx_en_d2p;
  logic        cio_pattgen_pcl0_tx_d2p;
  logic        cio_pattgen_pcl0_tx_en_d2p;
  logic        cio_pattgen_pda1_tx_d2p;
  logic        cio_pattgen_pda1_tx_en_d2p;
  logic        cio_pattgen_pcl1_tx_d2p;
  logic        cio_pattgen_pcl1_tx_en_d2p;
  // keymgr
  // csrng
  // entropy_src
  // otbn


  logic [139:0]  intr_vector;
  // Interrupt source list
  logic intr_uart_tx_watermark;
  logic intr_uart_rx_watermark;
  logic intr_uart_tx_empty;
  logic intr_uart_rx_overflow;
  logic intr_uart_rx_frame_err;
  logic intr_uart_rx_break_err;
  logic intr_uart_rx_timeout;
  logic intr_uart_rx_parity_err;
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
  logic intr_flash_ctrl_prog_empty;
  logic intr_flash_ctrl_prog_lvl;
  logic intr_flash_ctrl_rd_full;
  logic intr_flash_ctrl_rd_lvl;
  logic intr_flash_ctrl_op_done;
  logic intr_flash_ctrl_op_error;
  logic intr_rv_timer_timer_expired_0_0;
  logic intr_i2c0_fmt_watermark;
  logic intr_i2c0_rx_watermark;
  logic intr_i2c0_fmt_overflow;
  logic intr_i2c0_rx_overflow;
  logic intr_i2c0_nak;
  logic intr_i2c0_scl_interference;
  logic intr_i2c0_sda_interference;
  logic intr_i2c0_stretch_timeout;
  logic intr_i2c0_sda_unstable;
  logic intr_i2c1_fmt_watermark;
  logic intr_i2c1_rx_watermark;
  logic intr_i2c1_fmt_overflow;
  logic intr_i2c1_rx_overflow;
  logic intr_i2c1_nak;
  logic intr_i2c1_scl_interference;
  logic intr_i2c1_sda_interference;
  logic intr_i2c1_stretch_timeout;
  logic intr_i2c1_sda_unstable;
  logic intr_i2c2_fmt_watermark;
  logic intr_i2c2_rx_watermark;
  logic intr_i2c2_fmt_overflow;
  logic intr_i2c2_rx_overflow;
  logic intr_i2c2_nak;
  logic intr_i2c2_scl_interference;
  logic intr_i2c2_sda_interference;
  logic intr_i2c2_stretch_timeout;
  logic intr_i2c2_sda_unstable;
  logic intr_otp_ctrl_otp_access_done;
  logic intr_otp_ctrl_otp_ctrl_err;
  logic intr_hmac_hmac_done;
  logic intr_hmac_fifo_empty;
  logic intr_hmac_hmac_err;
  logic intr_kmac_kmac_done;
  logic intr_kmac_fifo_empty;
  logic intr_kmac_kmac_err;
  logic intr_alert_handler_classa;
  logic intr_alert_handler_classb;
  logic intr_alert_handler_classc;
  logic intr_alert_handler_classd;
  logic intr_pwrmgr_aon_wakeup;
  logic intr_timer_aon_timer_expired_0_0;
  logic intr_nmi_gen_esc0;
  logic intr_nmi_gen_esc1;
  logic intr_nmi_gen_esc2;
  logic intr_nmi_gen_esc3;
  logic intr_usbdev_aon_pkt_received;
  logic intr_usbdev_aon_pkt_sent;
  logic intr_usbdev_aon_disconnected;
  logic intr_usbdev_aon_host_lost;
  logic intr_usbdev_aon_link_reset;
  logic intr_usbdev_aon_link_suspend;
  logic intr_usbdev_aon_link_resume;
  logic intr_usbdev_aon_av_empty;
  logic intr_usbdev_aon_rx_full;
  logic intr_usbdev_aon_av_overflow;
  logic intr_usbdev_aon_link_in_err;
  logic intr_usbdev_aon_rx_crc_err;
  logic intr_usbdev_aon_rx_pid_err;
  logic intr_usbdev_aon_rx_bitstuff_err;
  logic intr_usbdev_aon_frame;
  logic intr_usbdev_aon_connected;
  logic intr_pattgen_patt_done0;
  logic intr_pattgen_patt_done1;
  logic intr_keymgr_op_done;
  logic intr_csrng_cs_cmd_req_done;
  logic intr_csrng_cs_fifo_err;
  logic intr_entropy_src_es_entropy_valid;
  logic intr_entropy_src_es_rct_failed;
  logic intr_entropy_src_es_apt_failed;
  logic intr_entropy_src_es_fifo_err;
  logic intr_otbn_done;
  logic intr_otbn_err;



  logic [0:0] irq_plic;
  logic [0:0] msip;
  logic [7:0] irq_id[1];
  logic [7:0] unused_irq_id[1];

  // this avoids lint errors
  assign unused_irq_id = irq_id;

  // Alert list
  prim_alert_pkg::alert_tx_t [alert_pkg::NAlerts-1:0]  alert_tx;
  prim_alert_pkg::alert_rx_t [alert_pkg::NAlerts-1:0]  alert_rx;
  // Escalation outputs
  prim_esc_pkg::esc_tx_t [alert_pkg::N_ESC_SEV-1:0]  esc_tx;
  prim_esc_pkg::esc_rx_t [alert_pkg::N_ESC_SEV-1:0]  esc_rx;


  // define inter-module signals
  flash_ctrl_pkg::flash_req_t       flash_ctrl_flash_req;
  flash_ctrl_pkg::flash_rsp_t       flash_ctrl_flash_rsp;
  otp_ctrl_pkg::flash_key_t       otp_ctrl_otp_flash_key;
  otp_ctrl_pkg::ram_main_key_t       otp_ctrl_otp_ram_main_key;
  otp_ctrl_pkg::ram_ret_aon_key_t       otp_ctrl_otp_ram_ret_aon_key;
  otbn_pkg::otbn_ram_key_t       otp_ctrl_otp_otbn_ram_key;
  otp_ctrl_pkg::lc_otp_program_req_t       otp_ctrl_lc_otp_program_req;
  otp_ctrl_pkg::lc_otp_program_rsp_t       otp_ctrl_lc_otp_program_rsp;
  otp_ctrl_pkg::otp_lc_data_t       otp_ctrl_otp_lc_data;
  lifecycle_pkg::lc_tx_t       lifecycle_nvm_debug;
  lifecycle_pkg::lc_tx_t       lifecycle_provision;
  pinmux_pkg::lc_strap_req_t       lifecycle_strap_sample_req;
  pinmux_pkg::lc_strap_rsp_t       lifecycle_strap_sample_rsp;
  pwrmgr_pkg::pwr_otp_req_t       pwrmgr_aon_pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_aon_pwr_otp_rsp;
  pwrmgr_pkg::pwr_rst_req_t       pwrmgr_aon_pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t       pwrmgr_aon_pwr_rst_rsp;
  pwrmgr_pkg::pwr_clk_req_t       pwrmgr_aon_pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t       pwrmgr_aon_pwr_clk_rsp;
  pwrmgr_pkg::pwr_lc_req_t       pwrmgr_aon_pwr_lc_req;
  pwrmgr_pkg::pwr_lc_rsp_t       pwrmgr_aon_pwr_lc_rsp;
  entropy_src_pkg::entropy_src_hw_if_req_t       csrng_entropy_src_hw_if_req;
  entropy_src_pkg::entropy_src_hw_if_rsp_t       csrng_entropy_src_hw_if_rsp;
  keymgr_pkg::hw_key_req_t       keymgr_kmac_key;
  keymgr_pkg::kmac_data_req_t       keymgr_kmac_data_req;
  keymgr_pkg::kmac_data_rsp_t       keymgr_kmac_data_rsp;
  logic       pwrmgr_aon_wakeups;
  rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets;
  rstmgr_pkg::rstmgr_cpu_t       rstmgr_aon_cpu;
  pwrmgr_pkg::pwr_cpu_t       pwrmgr_aon_pwr_cpu;
  clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks;
  csrng_pkg::csrng_req_t [2:0] csrng_csrng_cmd_req;
  csrng_pkg::csrng_rsp_t [2:0] csrng_csrng_cmd_rsp;

  assign csrng_csrng_cmd_req = '0;

  // Non-debug module reset == reset for everything except for the debug module
  logic ndmreset_req;

  // debug request from rv_dm to core
  logic debug_req;

  // processor core
  rv_core_ibex #(
    .PMPEnable                (1),
    .PMPGranularity           (0), // 2^(PMPGranularity+2) == 4 byte granularity
    .PMPNumRegions            (16),
    .MHPMCounterNum           (8),
    .MHPMCounterWidth         (40),
    .RV32E                    (0),
    .RV32M                    (1),
    .BranchTargetALU          (1),
    .WritebackStage           (1),
    .MultiplierImplementation ("single-cycle"),
    .DbgTriggerEn             (1),
    .DmHaltAddr               (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr          (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress),
    .PipeLine                 (IbexPipeLine)
  ) u_rv_core_ibex (
    // clock and reset
    .clk_i                (clkmgr_aon_clocks.clk_proc_main),
    .rst_ni               (rstmgr_aon_resets.rst_sys_n),
    .test_en_i            (1'b0),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_ROM),
    // TL-UL buses
    .tl_i_o               (tl_corei_h_h2d),
    .tl_i_i               (tl_corei_h_d2h),
    .tl_d_o               (tl_cored_h_h2d),
    .tl_d_i               (tl_cored_h_d2h),
    // interrupts
    .irq_software_i       (msip),
    .irq_timer_i          (intr_rv_timer_timer_expired_0_0),
    .irq_external_i       (irq_plic),
    .irq_fast_i           (15'b0),// PLIC handles all peripheral interrupts
    .irq_nm_i             (1'b0),// TODO - add and connect alert responder
    // debug interface
    .debug_req_i          (debug_req),
    // CPU control signals
    .fetch_enable_i       (1'b1),
    .core_sleep_o         (pwrmgr_aon_pwr_cpu.core_sleeping)
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  rv_dm #(
    .NrHarts     (1),
    .IdcodeValue (JTAG_IDCODE)
  ) u_dm_top (
    .clk_i         (clkmgr_aon_clocks.clk_proc_main),
    .rst_ni        (rstmgr_aon_resets.rst_lc_n),
    .testmode_i    (1'b0),
    .ndmreset_o    (ndmreset_req),
    .dmactive_o    (),
    .debug_req_o   (debug_req),
    .unavailable_i (1'b0),

    // bus device with debug memory (for execution-based debug)
    .tl_d_i        (tl_debug_mem_d_h2d),
    .tl_d_o        (tl_debug_mem_d_d2h),

    // bus host (for system bus accesses, SBA)
    .tl_h_o        (tl_dm_sba_h_h2d),
    .tl_h_i        (tl_dm_sba_h_d2h),

    //JTAG
    .tck_i            (jtag_tck_i),
    .tms_i            (jtag_tms_i),
    .trst_ni          (jtag_trst_ni),
    .td_i             (jtag_tdi_i),
    .td_o             (jtag_tdo_o),
    .tdo_oe_o         (       )
  );

  assign rstmgr_aon_cpu.ndmreset_req = ndmreset_req;
  assign rstmgr_aon_cpu.rst_cpu_n = rstmgr_aon_resets.rst_sys_n;

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
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_sys_n),

    .tl_i     (tl_rom_d_h2d),
    .tl_o     (tl_rom_d_d2h),

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
    .Depth(4096)
  ) u_rom_rom (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_sys_n),
    .req_i    (rom_req),
    .addr_i   (rom_addr),
    .rdata_o  (rom_rdata),
    .rvalid_o (rom_rvalid),
    .cfg_i    ('0) // tied off for now
  );

  // sram device
  logic        ram_main_req;
  logic        ram_main_we;
  logic [14:0] ram_main_addr;
  logic [31:0] ram_main_wdata;
  logic [31:0] ram_main_wmask;
  logic [31:0] ram_main_rdata;
  logic        ram_main_rvalid;
  logic [1:0]  ram_main_rerror;
  logic [127:0] ram_main_key;
  logic [48:0] ram_main_data_nonce;
  logic [14:0] ram_main_addr_nonce;

  // Note that this connection will change once we move to a fully comportable SRAM IP
  assign ram_main_data_nonce = otp_ctrl_otp_ram_main_key.nonce[49-1:0];
  assign ram_main_addr_nonce = otp_ctrl_otp_ram_main_key.nonce[49+15-1:49];
  assign ram_main_key = otp_ctrl_otp_ram_main_key.key;

  tlul_adapter_sram #(
    .SramAw(15),
    .SramDw(32),
    .Outstanding(2)
  ) u_tl_adapter_ram_main (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_sys_n),
    .tl_i     (tl_ram_main_d_h2d),
    .tl_o     (tl_ram_main_d_d2h),

    .req_o    (ram_main_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
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
    .Depth(32768),
    .DataBitsPerMask(8),
    .CfgW(8)
  ) u_ram1p_ram_main (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_sys_n),

    .key_i        ( ram_main_key ),
    .data_nonce_i ( ram_main_data_nonce ),
    .addr_nonce_i ( ram_main_addr_nonce ),

    .req_i    (ram_main_req),
    .write_i  (ram_main_we),
    .addr_i   (ram_main_addr),
    .wdata_i  (ram_main_wdata),
    .wmask_i  (ram_main_wmask),
    .rdata_o  (ram_main_rdata),
    .rvalid_o (ram_main_rvalid),
    .rerror_o (ram_main_rerror),
    .cfg_i    ('0)
  );
  // sram device
  logic        ram_ret_aon_req;
  logic        ram_ret_aon_we;
  logic [9:0] ram_ret_aon_addr;
  logic [31:0] ram_ret_aon_wdata;
  logic [31:0] ram_ret_aon_wmask;
  logic [31:0] ram_ret_aon_rdata;
  logic        ram_ret_aon_rvalid;
  logic [1:0]  ram_ret_aon_rerror;
  logic [127:0] ram_ret_aon_key;
  logic [53:0] ram_ret_aon_data_nonce;
  logic [9:0] ram_ret_aon_addr_nonce;

  // Note that this connection will change once we move to a fully comportable SRAM IP
  assign ram_ret_aon_data_nonce = otp_ctrl_otp_ram_ret_aon_key.nonce[54-1:0];
  assign ram_ret_aon_addr_nonce = otp_ctrl_otp_ram_ret_aon_key.nonce[54+10-1:54];
  assign ram_ret_aon_key = otp_ctrl_otp_ram_ret_aon_key.key;

  tlul_adapter_sram #(
    .SramAw(10),
    .SramDw(32),
    .Outstanding(2)
  ) u_tl_adapter_ram_ret_aon (
    .clk_i   (clkmgr_aon_clocks.clk_io_infra),
    .rst_ni   (rstmgr_aon_resets.rst_sys_io_n),
    .tl_i     (tl_ram_ret_aon_d_h2d),
    .tl_o     (tl_ram_ret_aon_d_d2h),

    .req_o    (ram_ret_aon_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (ram_ret_aon_we),
    .addr_o   (ram_ret_aon_addr),
    .wdata_o  (ram_ret_aon_wdata),
    .wmask_o  (ram_ret_aon_wmask),
    .rdata_i  (ram_ret_aon_rdata),
    .rvalid_i (ram_ret_aon_rvalid),
    .rerror_i (ram_ret_aon_rerror)
  );

  prim_ram_1p_scr #(
    .Width(32),
    .Depth(1024),
    .DataBitsPerMask(8),
    .CfgW(8)
  ) u_ram1p_ram_ret_aon (
    .clk_i   (clkmgr_aon_clocks.clk_io_infra),
    .rst_ni   (rstmgr_aon_resets.rst_sys_io_n),

    .key_i        ( ram_ret_aon_key ),
    .data_nonce_i ( ram_ret_aon_data_nonce ),
    .addr_nonce_i ( ram_ret_aon_addr_nonce ),

    .req_i    (ram_ret_aon_req),
    .write_i  (ram_ret_aon_we),
    .addr_i   (ram_ret_aon_addr),
    .wdata_i  (ram_ret_aon_wdata),
    .wmask_i  (ram_ret_aon_wmask),
    .rdata_o  (ram_ret_aon_rdata),
    .rvalid_o (ram_ret_aon_rvalid),
    .rerror_o (ram_ret_aon_rerror),
    .cfg_i    ('0)
  );

  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;

  tlul_adapter_sram #(
    .SramAw(flash_ctrl_pkg::BusAddrW),
    .SramDw(flash_ctrl_pkg::BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1)
  ) u_tl_adapter_eflash (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n),

    .tl_i       (tl_eflash_d_h2d),
    .tl_o       (tl_eflash_d_d2h),

    .req_o    (flash_host_req),
    .gnt_i    (flash_host_req_rdy),
    .we_o     (),
    .addr_o   (flash_host_addr),
    .wdata_o  (),
    .wmask_o  (),
    .rdata_i  (flash_host_rdata),
    .rvalid_i (flash_host_req_done),
    .rerror_i (2'b00)
  );

  flash_phy u_flash_eflash (
    .clk_i   (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n),
    .host_req_i      (flash_host_req),
    .host_addr_i     (flash_host_addr),
    .host_req_rdy_o  (flash_host_req_rdy),
    .host_req_done_o (flash_host_req_done),
    .host_rdata_o    (flash_host_rdata),
    .flash_ctrl_i    (flash_ctrl_flash_req),
    .flash_ctrl_o    (flash_ctrl_flash_rsp)
  );



  uart u_uart (
      .tl_i (tl_uart_d_h2d),
      .tl_o (tl_uart_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  uart u_uart1 (
      .tl_i (tl_uart1_d_h2d),
      .tl_o (tl_uart1_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  uart u_uart2 (
      .tl_i (tl_uart2_d_h2d),
      .tl_o (tl_uart2_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  uart u_uart3 (
      .tl_i (tl_uart3_d_h2d),
      .tl_o (tl_uart3_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  gpio u_gpio (
      .tl_i (tl_gpio_d_h2d),
      .tl_o (tl_gpio_d_d2h),

      // Input
      .cio_gpio_i    (cio_gpio_gpio_p2d),

      // Output
      .cio_gpio_o    (cio_gpio_gpio_d2p),
      .cio_gpio_en_o (cio_gpio_gpio_en_d2p),

      // Interrupt
      .intr_gpio_o (intr_gpio_gpio),

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  spi_device u_spi_device (
      .tl_i (tl_spi_device_d_h2d),
      .tl_o (tl_spi_device_d_d2h),

      // Input
      .cio_sck_i     (cio_spi_device_sck_p2d),
      .cio_csb_i     (cio_spi_device_csb_p2d),
      .cio_mosi_i    (cio_spi_device_mosi_p2d),

      // Output
      .cio_miso_o    (cio_spi_device_miso_d2p),
      .cio_miso_en_o (cio_spi_device_miso_en_d2p),

      // Interrupt
      .intr_rxf_o         (intr_spi_device_rxf),
      .intr_rxlvl_o       (intr_spi_device_rxlvl),
      .intr_txlvl_o       (intr_spi_device_txlvl),
      .intr_rxerr_o       (intr_spi_device_rxerr),
      .intr_rxoverflow_o  (intr_spi_device_rxoverflow),
      .intr_txunderflow_o (intr_spi_device_txunderflow),
      .scanmode_i   (scanmode_i),

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_spi_device_n)
  );

  flash_ctrl u_flash_ctrl (
      .tl_i (tl_flash_ctrl_d_h2d),
      .tl_o (tl_flash_ctrl_d_d2h),

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
      .otp_i(otp_ctrl_otp_flash_key),

      .clk_i (clkmgr_aon_clocks.clk_main_infra),
      .rst_ni (rstmgr_aon_resets.rst_lc_n)
  );

  rv_timer u_rv_timer (
      .tl_i (tl_rv_timer_d_h2d),
      .tl_o (tl_rv_timer_d_d2h),

      // Interrupt
      .intr_timer_expired_0_0_o (intr_rv_timer_timer_expired_0_0),

      .clk_i (clkmgr_aon_clocks.clk_io_timers),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  i2c u_i2c0 (
      .tl_i (tl_i2c0_d_h2d),
      .tl_o (tl_i2c0_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  i2c u_i2c1 (
      .tl_i (tl_i2c1_d_h2d),
      .tl_o (tl_i2c1_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  i2c u_i2c2 (
      .tl_i (tl_i2c2_d_h2d),
      .tl_o (tl_i2c2_d_d2h),

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

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  sensor_ctrl u_sensor_ctrl (
      .tl_i (tl_sensor_ctrl_d_h2d),
      .tl_o (tl_sensor_ctrl_d_d2h),

      // [0]: ast_alerts
      .alert_tx_o  ( alert_tx[6:0] ),
      .alert_rx_i  ( alert_rx[6:0] ),

      // Inter-module signals
      .ast_host_o(sensor_ctrl_ast_host),
      .ast_dev_i(sensor_ctrl_ast_dev),
      .ast_aux_o(sensor_ctrl_ast_aux),
      .ast_alert_i(sensor_ctrl_ast_alert_req),
      .ast_alert_o(sensor_ctrl_ast_alert_rsp),
      .ast_status_i(sensor_ctrl_ast_status),

      .clk_i (clkmgr_aon_clocks.clk_io_secure),
      .clk_aon_i (clkmgr_aon_clocks.clk_aon_secure),
      .clk_sys_i (clkmgr_aon_clocks.clk_main_secure),
      .clk_usb_i (clkmgr_aon_clocks.clk_usb_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n),
      .rst_aon_ni (rstmgr_aon_resets.rst_por_aon_n),
      .rst_sys_ni (rstmgr_aon_resets.rst_sys_n),
      .rst_usb_ni (rstmgr_aon_resets.rst_usb_n)
  );

  otp_ctrl u_otp_ctrl (
      .tl_i (tl_otp_ctrl_d_h2d),
      .tl_o (tl_otp_ctrl_d_d2h),

      // Interrupt
      .intr_otp_access_done_o (intr_otp_ctrl_otp_access_done),
      .intr_otp_ctrl_err_o    (intr_otp_ctrl_otp_ctrl_err),

      // [1]: otp_reg_parity_mismatch
      // [2]: otp_reg_digest_mismatch
      .alert_tx_o  ( alert_tx[2:1] ),
      .alert_rx_i  ( alert_rx[2:1] ),

      // Inter-module signals
      .pwr_otp_init_i(pwrmgr_aon_pwr_otp_req),
      .pwr_otp_init_o(pwrmgr_aon_pwr_otp_rsp),
      .otp_pwr_state_o(),
      .lc_otp_program_i(otp_ctrl_lc_otp_program_req),
      .lc_otp_program_o(otp_ctrl_lc_otp_program_rsp),
      .otp_lc_data_o(otp_ctrl_otp_lc_data),
      .lc_provision_en_i(lifecycle_provision),
      .lc_test_en_i(lifecycle_nvm_debug),
      .otp_keymgr_key_o(),
      .otp_flash_key_o(otp_ctrl_otp_flash_key),
      .otp_ram_main_key_o(otp_ctrl_otp_ram_main_key),
      .otp_ram_ret_aon_key_o(otp_ctrl_otp_ram_ret_aon_key),
      .otp_otbn_ram_key_o(otp_ctrl_otp_otbn_ram_key),

      .clk_i (clkmgr_aon_clocks.clk_io_secure),
      .rst_ni (rstmgr_aon_resets.rst_lc_n)
  );

  lifecycle u_lifecycle (
      .tl_i (tl_lifecycle_d_h2d),
      .tl_o (tl_lifecycle_d_d2h),

      // Inter-module signals
      .pwrmgr_i(pwrmgr_aon_pwr_lc_req),
      .pwrmgr_o(pwrmgr_aon_pwr_lc_rsp),
      .otp_program_o(otp_ctrl_lc_otp_program_req),
      .otp_program_i(otp_ctrl_lc_otp_program_rsp),
      .otp_data_i(otp_ctrl_otp_lc_data),
      .dft_o(),
      .hw_debug_o(),
      .nvm_debug_o(lifecycle_nvm_debug),
      .cpu_o(),
      .provision_o(lifecycle_provision),
      .keymgr_o(),
      .strap_sample_o(lifecycle_strap_sample_req),
      .strap_sample_i(lifecycle_strap_sample_rsp),

      .clk_i (clkmgr_aon_clocks.clk_io_secure),
      .rst_ni (rstmgr_aon_resets.rst_lc_n)
  );

  aes u_aes (
      .tl_i (tl_aes_d_h2d),
      .tl_o (tl_aes_d_d2h),

      .clk_i (clkmgr_aon_clocks.clk_main_aes),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  hmac u_hmac (
      .tl_i (tl_hmac_d_h2d),
      .tl_o (tl_hmac_d_d2h),

      // Interrupt
      .intr_hmac_done_o  (intr_hmac_hmac_done),
      .intr_fifo_empty_o (intr_hmac_fifo_empty),
      .intr_hmac_err_o   (intr_hmac_hmac_err),

      // [3]: msg_push_sha_disabled
      .alert_tx_o  ( alert_tx[3:3] ),
      .alert_rx_i  ( alert_rx[3:3] ),

      .clk_i (clkmgr_aon_clocks.clk_main_hmac),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  kmac u_kmac (
      .tl_i (tl_kmac_d_h2d),
      .tl_o (tl_kmac_d_d2h),

      // Interrupt
      .intr_kmac_done_o  (intr_kmac_kmac_done),
      .intr_fifo_empty_o (intr_kmac_fifo_empty),
      .intr_kmac_err_o   (intr_kmac_kmac_err),

      // [4]: sram_uncorrectable
      // [5]: data_parity
      .alert_tx_o  ( alert_tx[5:4] ),
      .alert_rx_i  ( alert_rx[5:4] ),

      // Inter-module signals
      .keymgr_key_i(keymgr_kmac_key),
      .keymgr_data_i(keymgr_kmac_data_req),
      .keymgr_data_o(keymgr_kmac_data_rsp),

      .clk_i (clkmgr_aon_clocks.clk_main_kmac),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  rv_plic u_rv_plic (
      .tl_i (tl_rv_plic_d_h2d),
      .tl_o (tl_rv_plic_d_d2h),

      .intr_src_i (intr_vector),
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),

      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  pinmux u_pinmux_aon (
      .tl_i (tl_pinmux_aon_d_h2d),
      .tl_o (tl_pinmux_aon_d_d2h),

      // Inter-module signals
      .lc_pinmux_strap_i(lifecycle_strap_sample_req),
      .lc_pinmux_strap_o(lifecycle_strap_sample_rsp),
      .sleep_en_i('0),
      .aon_wkup_req_o(pwrmgr_aon_wakeups),

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

      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .clk_aon_i (clkmgr_aon_clocks.clk_io_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n),
      .rst_aon_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  padctrl u_padctrl_aon (
      .tl_i (tl_padctrl_aon_d_h2d),
      .tl_o (tl_padctrl_aon_d_d2h),

      .mio_attr_o,
      .dio_attr_o,

      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  alert_handler u_alert_handler (
      .tl_i (tl_alert_handler_d_h2d),
      .tl_o (tl_alert_handler_d_d2h),

      // Interrupt
      .intr_classa_o (intr_alert_handler_classa),
      .intr_classb_o (intr_alert_handler_classb),
      .intr_classc_o (intr_alert_handler_classc),
      .intr_classd_o (intr_alert_handler_classd),
      // TODO: wire this to hardware debug circuit
      .crashdump_o (          ),
      // TODO: wire this to TRNG
      .entropy_i   ( 1'b0     ),
      // alert signals
      .alert_rx_o  ( alert_rx ),
      .alert_tx_i  ( alert_tx ),
      // escalation outputs
      .esc_rx_i    ( esc_rx   ),
      .esc_tx_o    ( esc_tx   ),

      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  pwrmgr u_pwrmgr_aon (
      .tl_i (tl_pwrmgr_aon_d_h2d),
      .tl_o (tl_pwrmgr_aon_d_d2h),

      // Interrupt
      .intr_wakeup_o (intr_pwrmgr_aon_wakeup),

      // Inter-module signals
      .pwr_ast_o(pwrmgr_aon_pwr_ast_req),
      .pwr_ast_i(pwrmgr_aon_pwr_ast_rsp),
      .pwr_rst_o(pwrmgr_aon_pwr_rst_req),
      .pwr_rst_i(pwrmgr_aon_pwr_rst_rsp),
      .pwr_clk_o(pwrmgr_aon_pwr_clk_req),
      .pwr_clk_i(pwrmgr_aon_pwr_clk_rsp),
      .pwr_otp_o(pwrmgr_aon_pwr_otp_req),
      .pwr_otp_i(pwrmgr_aon_pwr_otp_rsp),
      .pwr_lc_o(pwrmgr_aon_pwr_lc_req),
      .pwr_lc_i(pwrmgr_aon_pwr_lc_rsp),
      .pwr_flash_i(pwrmgr_pkg::PWR_FLASH_DEFAULT),
      .pwr_cpu_i(pwrmgr_aon_pwr_cpu),
      .wakeups_i(pwrmgr_aon_wakeups),
      .rstreqs_i('0),

      .clk_i (clk_io_i),
      .clk_slow_i (clk_aon_i),
      .rst_ni (rstmgr_aon_resets.rst_por_n),
      .rst_slow_ni (rstmgr_aon_resets.rst_por_aon_n)
  );

  rstmgr u_rstmgr_aon (
      .tl_i (tl_rstmgr_aon_d_h2d),
      .tl_o (tl_rstmgr_aon_d_d2h),

      // Inter-module signals
      .pwr_i(pwrmgr_aon_pwr_rst_req),
      .pwr_o(pwrmgr_aon_pwr_rst_rsp),
      .resets_o(rstmgr_aon_resets),
      .ast_i(rstmgr_aon_ast),
      .cpu_i(rstmgr_aon_cpu),
      .peri_i(rstmgr_pkg::RSTMGR_PERI_DEFAULT),

      .clk_i (clk_io_i),
      .clk_aon_i (clk_aon_i),
      .clk_main_i (clk_i),
      .clk_io_i (clk_io_i),
      .clk_usb_i (clk_usb_i),
      .rst_ni (rst_ni)
  );

  clkmgr u_clkmgr_aon (
      .tl_i (tl_clkmgr_aon_d_h2d),
      .tl_o (tl_clkmgr_aon_d_d2h),

      // Inter-module signals
      .clocks_o(clkmgr_aon_clocks),
      .pwr_i(pwrmgr_aon_pwr_clk_req),
      .pwr_o(pwrmgr_aon_pwr_clk_rsp),
      .dft_i(clkmgr_pkg::CLK_DFT_DEFAULT),
      .status_i(clkmgr_pkg::CLK_HINT_STATUS_DEFAULT),

      .clk_i (clk_io_i),
      .clk_main_i (clk_i),
      .clk_io_i (clk_io_i),
      .clk_usb_i (clk_usb_i),
      .clk_aon_i (clk_aon_i),
      .rst_ni (rstmgr_aon_resets.rst_por_io_n),
      .rst_main_ni (rstmgr_aon_resets.rst_por_n),
      .rst_io_ni (rstmgr_aon_resets.rst_por_io_n),
      .rst_usb_ni (rstmgr_aon_resets.rst_por_usb_n)
  );

  rbox u_rbox_aon (
      .tl_i (tl_rbox_aon_d_h2d),
      .tl_o (tl_rbox_aon_d_d2h),

      // Input
      .cio_ac_present_i        (cio_rbox_aon_ac_present_p2d),
      .cio_ec_entering_rw_i    (cio_rbox_aon_ec_entering_rw_p2d),
      .cio_key0_in_i           (cio_rbox_aon_key0_in_p2d),
      .cio_key1_in_i           (cio_rbox_aon_key1_in_p2d),
      .cio_key2_in_i           (cio_rbox_aon_key2_in_p2d),
      .cio_pwrb_in_i           (cio_rbox_aon_pwrb_in_p2d),

      // Output
      .cio_bat_en_o            (cio_rbox_aon_bat_en_d2p),
      .cio_bat_en_en_o         (cio_rbox_aon_bat_en_en_d2p),
      .cio_ec_in_rw_o          (cio_rbox_aon_ec_in_rw_d2p),
      .cio_ec_in_rw_en_o       (cio_rbox_aon_ec_in_rw_en_d2p),
      .cio_ec_rst_l_o          (cio_rbox_aon_ec_rst_l_d2p),
      .cio_ec_rst_l_en_o       (cio_rbox_aon_ec_rst_l_en_d2p),
      .cio_flash_wp_l_o        (cio_rbox_aon_flash_wp_l_d2p),
      .cio_flash_wp_l_en_o     (cio_rbox_aon_flash_wp_l_en_d2p),
      .cio_key0_out_o          (cio_rbox_aon_key0_out_d2p),
      .cio_key0_out_en_o       (cio_rbox_aon_key0_out_en_d2p),
      .cio_key1_out_o          (cio_rbox_aon_key1_out_d2p),
      .cio_key1_out_en_o       (cio_rbox_aon_key1_out_en_d2p),
      .cio_key2_out_o          (cio_rbox_aon_key2_out_d2p),
      .cio_key2_out_en_o       (cio_rbox_aon_key2_out_en_d2p),
      .cio_pwrb_out_o          (cio_rbox_aon_pwrb_out_d2p),
      .cio_pwrb_out_en_o       (cio_rbox_aon_pwrb_out_en_d2p),

      .clk_i (clk_io_i),
      .rst_ni (rstmgr_aon_resets.rst_por_io_n),
      .sw_rst_ni (rstmgr_aon_resets.rst_por_io_n)
  );

  pwm u_pwm_aon (
      .tl_i (tl_pwm_aon_d_h2d),
      .tl_o (tl_pwm_aon_d_d2h),

      // Output
      .cio_pwm_o    (cio_pwm_aon_pwm_d2p),
      .cio_pwm_en_o (cio_pwm_aon_pwm_en_d2p),

      .clk_i (clk_io_i),
      .rst_ni (rstmgr_aon_resets.rst_por_io_n)
  );

  rv_timer u_timer_aon (
      .tl_i (tl_timer_aon_d_h2d),
      .tl_o (tl_timer_aon_d_d2h),

      // Interrupt
      .intr_timer_expired_0_0_o (intr_timer_aon_timer_expired_0_0),

      .clk_i (clk_aon_i),
      .rst_ni (rstmgr_aon_resets.rst_por_aon_n)
  );

  nmi_gen u_nmi_gen (
      .tl_i (tl_nmi_gen_d_h2d),
      .tl_o (tl_nmi_gen_d_d2h),

      // Interrupt
      .intr_esc0_o (intr_nmi_gen_esc0),
      .intr_esc1_o (intr_nmi_gen_esc1),
      .intr_esc2_o (intr_nmi_gen_esc2),
      .intr_esc3_o (intr_nmi_gen_esc3),
      // escalation signal inputs
      .esc_rx_o    ( esc_rx   ),
      .esc_tx_i    ( esc_tx   ),

      .clk_i (clkmgr_aon_clocks.clk_main_secure),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  usbdev u_usbdev_aon (
      .tl_i (tl_usbdev_aon_d_h2d),
      .tl_o (tl_usbdev_aon_d_d2h),

      // Input
      .cio_sense_i         (cio_usbdev_aon_sense_p2d),
      .cio_d_i             (cio_usbdev_aon_d_p2d),
      .cio_dp_i            (cio_usbdev_aon_dp_p2d),
      .cio_dn_i            (cio_usbdev_aon_dn_p2d),

      // Output
      .cio_se0_o           (cio_usbdev_aon_se0_d2p),
      .cio_se0_en_o        (cio_usbdev_aon_se0_en_d2p),
      .cio_dp_pullup_o     (cio_usbdev_aon_dp_pullup_d2p),
      .cio_dp_pullup_en_o  (cio_usbdev_aon_dp_pullup_en_d2p),
      .cio_dn_pullup_o     (cio_usbdev_aon_dn_pullup_d2p),
      .cio_dn_pullup_en_o  (cio_usbdev_aon_dn_pullup_en_d2p),
      .cio_tx_mode_se_o    (cio_usbdev_aon_tx_mode_se_d2p),
      .cio_tx_mode_se_en_o (cio_usbdev_aon_tx_mode_se_en_d2p),
      .cio_suspend_o       (cio_usbdev_aon_suspend_d2p),
      .cio_suspend_en_o    (cio_usbdev_aon_suspend_en_d2p),
      .cio_d_o             (cio_usbdev_aon_d_d2p),
      .cio_d_en_o          (cio_usbdev_aon_d_en_d2p),
      .cio_dp_o            (cio_usbdev_aon_dp_d2p),
      .cio_dp_en_o         (cio_usbdev_aon_dp_en_d2p),
      .cio_dn_o            (cio_usbdev_aon_dn_d2p),
      .cio_dn_en_o         (cio_usbdev_aon_dn_en_d2p),

      // Interrupt
      .intr_pkt_received_o    (intr_usbdev_aon_pkt_received),
      .intr_pkt_sent_o        (intr_usbdev_aon_pkt_sent),
      .intr_disconnected_o    (intr_usbdev_aon_disconnected),
      .intr_host_lost_o       (intr_usbdev_aon_host_lost),
      .intr_link_reset_o      (intr_usbdev_aon_link_reset),
      .intr_link_suspend_o    (intr_usbdev_aon_link_suspend),
      .intr_link_resume_o     (intr_usbdev_aon_link_resume),
      .intr_av_empty_o        (intr_usbdev_aon_av_empty),
      .intr_rx_full_o         (intr_usbdev_aon_rx_full),
      .intr_av_overflow_o     (intr_usbdev_aon_av_overflow),
      .intr_link_in_err_o     (intr_usbdev_aon_link_in_err),
      .intr_rx_crc_err_o      (intr_usbdev_aon_rx_crc_err),
      .intr_rx_pid_err_o      (intr_usbdev_aon_rx_pid_err),
      .intr_rx_bitstuff_err_o (intr_usbdev_aon_rx_bitstuff_err),
      .intr_frame_o           (intr_usbdev_aon_frame),
      .intr_connected_o       (intr_usbdev_aon_connected),

      // Inter-module signals
      .usb_ref_val_o(usbdev_aon_usb_ref_val),
      .usb_ref_pulse_o(usbdev_aon_usb_ref_pulse),

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .clk_usb_48mhz_i (clkmgr_aon_clocks.clk_usb_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n),
      .rst_usb_48mhz_ni (rstmgr_aon_resets.rst_usb_n)
  );

  pattgen u_pattgen (
      .tl_i (tl_pattgen_d_h2d),
      .tl_o (tl_pattgen_d_d2h),

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
      .intr_patt_done0_o (intr_pattgen_patt_done0),
      .intr_patt_done1_o (intr_pattgen_patt_done1),

      .clk_i (clkmgr_aon_clocks.clk_io_peri),
      .rst_ni (rstmgr_aon_resets.rst_sys_io_n)
  );

  keymgr u_keymgr (
      .tl_i (tl_keymgr_d_h2d),
      .tl_o (tl_keymgr_d_d2h),

      // Interrupt
      .intr_op_done_o (intr_keymgr_op_done),

      // Inter-module signals
      .aes_key_o(),
      .hmac_key_o(),
      .kmac_key_o(keymgr_kmac_key),
      .kmac_data_o(keymgr_kmac_data_req),
      .kmac_data_i(keymgr_kmac_data_rsp),
      .lc_i(keymgr_pkg::LC_DATA_DEFAULT),
      .otp_i(keymgr_pkg::OTP_DATA_DEFAULT),
      .flash_i(keymgr_pkg::FLASH_KEY_DEFAULT),

      .clk_i (clkmgr_aon_clocks.clk_main_keymgr),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  csrng u_csrng (
      .tl_i (tl_csrng_d_h2d),
      .tl_o (tl_csrng_d_d2h),

      // Interrupt
      .intr_cs_cmd_req_done_o (intr_csrng_cs_cmd_req_done),
      .intr_cs_fifo_err_o     (intr_csrng_cs_fifo_err),

      // Inter-module signals
      .csrng_cmd_i(csrng_csrng_cmd_req),
      .csrng_cmd_o(csrng_csrng_cmd_rsp),
      .entropy_src_hw_if_o(csrng_entropy_src_hw_if_req),
      .entropy_src_hw_if_i(csrng_entropy_src_hw_if_rsp),
      .efuse_sw_app_enable_i('0),

      .clk_i (clkmgr_aon_clocks.clk_main_csrng),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  entropy_src u_entropy_src (
      .tl_i (tl_entropy_src_d_h2d),
      .tl_o (tl_entropy_src_d_d2h),

      // Interrupt
      .intr_es_entropy_valid_o (intr_entropy_src_es_entropy_valid),
      .intr_es_rct_failed_o    (intr_entropy_src_es_rct_failed),
      .intr_es_apt_failed_o    (intr_entropy_src_es_apt_failed),
      .intr_es_fifo_err_o      (intr_entropy_src_es_fifo_err),

      // Inter-module signals
      .entropy_src_hw_if_i(csrng_entropy_src_hw_if_req),
      .entropy_src_hw_if_o(csrng_entropy_src_hw_if_rsp),
      .entropy_src_rng_o(entropy_src_entropy_src_rng_req),
      .entropy_src_rng_i(entropy_src_entropy_src_rng_rsp),
      .efuse_es_sw_reg_en_i('0),

      .clk_i (clkmgr_aon_clocks.clk_main_entropy_src),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  otbn u_otbn (
      .tl_i (tl_otbn_d_h2d),
      .tl_o (tl_otbn_d_d2h),

      // Interrupt
      .intr_done_o (intr_otbn_done),
      .intr_err_o  (intr_otbn_err),

      // [6]: imem_uncorrectable
      // [7]: dmem_uncorrectable
      // [8]: reg_uncorrectable
      .alert_tx_o  ( alert_tx[8:6] ),
      .alert_rx_i  ( alert_rx[8:6] ),

      // Inter-module signals
      .idle_o(),
      .otp_otbn_ram_key_i(otp_ctrl_otp_otbn_ram_key),

      .clk_i (clkmgr_aon_clocks.clk_main_otbn),
      .rst_ni (rstmgr_aon_resets.rst_sys_n)
  );

  // interrupt assignments
  assign intr_vector = {
      intr_otbn_err,
      intr_otbn_done,
      intr_i2c2_sda_unstable,
      intr_i2c2_stretch_timeout,
      intr_i2c2_sda_interference,
      intr_i2c2_scl_interference,
      intr_i2c2_nak,
      intr_i2c2_rx_overflow,
      intr_i2c2_fmt_overflow,
      intr_i2c2_rx_watermark,
      intr_i2c2_fmt_watermark,
      intr_i2c1_sda_unstable,
      intr_i2c1_stretch_timeout,
      intr_i2c1_sda_interference,
      intr_i2c1_scl_interference,
      intr_i2c1_nak,
      intr_i2c1_rx_overflow,
      intr_i2c1_fmt_overflow,
      intr_i2c1_rx_watermark,
      intr_i2c1_fmt_watermark,
      intr_i2c0_sda_unstable,
      intr_i2c0_stretch_timeout,
      intr_i2c0_sda_interference,
      intr_i2c0_scl_interference,
      intr_i2c0_nak,
      intr_i2c0_rx_overflow,
      intr_i2c0_fmt_overflow,
      intr_i2c0_rx_watermark,
      intr_i2c0_fmt_watermark,
      intr_uart3_rx_parity_err,
      intr_uart3_rx_timeout,
      intr_uart3_rx_break_err,
      intr_uart3_rx_frame_err,
      intr_uart3_rx_overflow,
      intr_uart3_tx_empty,
      intr_uart3_rx_watermark,
      intr_uart3_tx_watermark,
      intr_uart2_rx_parity_err,
      intr_uart2_rx_timeout,
      intr_uart2_rx_break_err,
      intr_uart2_rx_frame_err,
      intr_uart2_rx_overflow,
      intr_uart2_tx_empty,
      intr_uart2_rx_watermark,
      intr_uart2_tx_watermark,
      intr_uart1_rx_parity_err,
      intr_uart1_rx_timeout,
      intr_uart1_rx_break_err,
      intr_uart1_rx_frame_err,
      intr_uart1_rx_overflow,
      intr_uart1_tx_empty,
      intr_uart1_rx_watermark,
      intr_uart1_tx_watermark,
      intr_otp_ctrl_otp_ctrl_err,
      intr_otp_ctrl_otp_access_done,
      intr_pwrmgr_aon_wakeup,
      intr_usbdev_aon_connected,
      intr_usbdev_aon_frame,
      intr_usbdev_aon_rx_bitstuff_err,
      intr_usbdev_aon_rx_pid_err,
      intr_usbdev_aon_rx_crc_err,
      intr_usbdev_aon_link_in_err,
      intr_usbdev_aon_av_overflow,
      intr_usbdev_aon_rx_full,
      intr_usbdev_aon_av_empty,
      intr_usbdev_aon_link_resume,
      intr_usbdev_aon_link_suspend,
      intr_usbdev_aon_link_reset,
      intr_usbdev_aon_host_lost,
      intr_usbdev_aon_disconnected,
      intr_usbdev_aon_pkt_sent,
      intr_usbdev_aon_pkt_received,
      intr_nmi_gen_esc3,
      intr_nmi_gen_esc2,
      intr_nmi_gen_esc1,
      intr_nmi_gen_esc0,
      intr_alert_handler_classd,
      intr_alert_handler_classc,
      intr_alert_handler_classb,
      intr_alert_handler_classa,
      intr_kmac_kmac_err,
      intr_kmac_fifo_empty,
      intr_kmac_kmac_done,
      intr_hmac_hmac_err,
      intr_hmac_fifo_empty,
      intr_hmac_hmac_done,
      intr_keymgr_op_done,
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
    .clk_main_i (clkmgr_aon_clocks.clk_main_infra),
    .clk_fixed_i (clkmgr_aon_clocks.clk_io_infra),
    .rst_main_ni (rstmgr_aon_resets.rst_sys_n),
    .rst_fixed_ni (rstmgr_aon_resets.rst_sys_io_n),
    .tl_corei_i         (tl_corei_h_h2d),
    .tl_corei_o         (tl_corei_h_d2h),
    .tl_cored_i         (tl_cored_h_h2d),
    .tl_cored_o         (tl_cored_h_d2h),
    .tl_dm_sba_i        (tl_dm_sba_h_h2d),
    .tl_dm_sba_o        (tl_dm_sba_h_d2h),
    .tl_rom_o           (tl_rom_d_h2d),
    .tl_rom_i           (tl_rom_d_d2h),
    .tl_debug_mem_o     (tl_debug_mem_d_h2d),
    .tl_debug_mem_i     (tl_debug_mem_d_d2h),
    .tl_ram_main_o      (tl_ram_main_d_h2d),
    .tl_ram_main_i      (tl_ram_main_d_d2h),
    .tl_eflash_o        (tl_eflash_d_h2d),
    .tl_eflash_i        (tl_eflash_d_d2h),
    .tl_peri_o          (tl_main_peri_h2d),
    .tl_peri_i          (tl_main_peri_d2h),
    .tl_aon_o           (tl_main_aon_h2d),
    .tl_aon_i           (tl_main_aon_d2h),
    .tl_flash_ctrl_o    (tl_flash_ctrl_d_h2d),
    .tl_flash_ctrl_i    (tl_flash_ctrl_d_d2h),
    .tl_hmac_o          (tl_hmac_d_h2d),
    .tl_hmac_i          (tl_hmac_d_d2h),
    .tl_kmac_o          (tl_kmac_d_h2d),
    .tl_kmac_i          (tl_kmac_d_d2h),
    .tl_aes_o           (tl_aes_d_h2d),
    .tl_aes_i           (tl_aes_d_d2h),
    .tl_keymgr_o        (tl_keymgr_d_h2d),
    .tl_keymgr_i        (tl_keymgr_d_d2h),
    .tl_rv_plic_o       (tl_rv_plic_d_h2d),
    .tl_rv_plic_i       (tl_rv_plic_d_d2h),
    .tl_alert_handler_o (tl_alert_handler_d_h2d),
    .tl_alert_handler_i (tl_alert_handler_d_d2h),
    .tl_csrng_o         (tl_csrng_d_h2d),
    .tl_csrng_i         (tl_csrng_d_d2h),
    .tl_entropy_src_o   (tl_entropy_src_d_h2d),
    .tl_entropy_src_i   (tl_entropy_src_d_d2h),
    .tl_nmi_gen_o       (tl_nmi_gen_d_h2d),
    .tl_nmi_gen_i       (tl_nmi_gen_d_d2h),
    .tl_otbn_o          (tl_otbn_d_h2d),
    .tl_otbn_i          (tl_otbn_d_d2h),

    .scanmode_i
  );
  xbar_peri u_xbar_peri (
    .clk_peri_i (clkmgr_aon_clocks.clk_io_infra),
    .rst_peri_ni (rstmgr_aon_resets.rst_sys_io_n),
    .tl_main_i        (tl_main_peri_h2d),
    .tl_main_o        (tl_main_peri_d2h),
    .tl_lifecycle_o   (tl_lifecycle_d_h2d),
    .tl_lifecycle_i   (tl_lifecycle_d_d2h),
    .tl_uart_o        (tl_uart_d_h2d),
    .tl_uart_i        (tl_uart_d_d2h),
    .tl_uart1_o       (tl_uart1_d_h2d),
    .tl_uart1_i       (tl_uart1_d_d2h),
    .tl_uart2_o       (tl_uart2_d_h2d),
    .tl_uart2_i       (tl_uart2_d_d2h),
    .tl_uart3_o       (tl_uart3_d_h2d),
    .tl_uart3_i       (tl_uart3_d_d2h),
    .tl_gpio_o        (tl_gpio_d_h2d),
    .tl_gpio_i        (tl_gpio_d_d2h),
    .tl_spi_device_o  (tl_spi_device_d_h2d),
    .tl_spi_device_i  (tl_spi_device_d_d2h),
    .tl_rv_timer_o    (tl_rv_timer_d_h2d),
    .tl_rv_timer_i    (tl_rv_timer_d_d2h),
    .tl_i2c0_o        (tl_i2c0_d_h2d),
    .tl_i2c0_i        (tl_i2c0_d_d2h),
    .tl_i2c1_o        (tl_i2c1_d_h2d),
    .tl_i2c1_i        (tl_i2c1_d_d2h),
    .tl_i2c2_o        (tl_i2c2_d_h2d),
    .tl_i2c2_i        (tl_i2c2_d_d2h),
    .tl_pattgen_o     (tl_pattgen_d_h2d),
    .tl_pattgen_i     (tl_pattgen_d_d2h),
    .tl_sensor_ctrl_o (tl_sensor_ctrl_d_h2d),
    .tl_sensor_ctrl_i (tl_sensor_ctrl_d_d2h),
    .tl_otp_ctrl_o    (tl_otp_ctrl_d_h2d),
    .tl_otp_ctrl_i    (tl_otp_ctrl_d_d2h),

    .scanmode_i
  );
  xbar_aon u_xbar_aon (
    .clk_aon_i (clkmgr_aon_clocks.clk_io_infra),
    .rst_aon_ni (rstmgr_aon_resets.rst_sys_io_n),
    .tl_main_i        (tl_main_aon_h2d),
    .tl_main_o        (tl_main_aon_d2h),
    .tl_pwrmgr_aon_o  (tl_pwrmgr_aon_d_h2d),
    .tl_pwrmgr_aon_i  (tl_pwrmgr_aon_d_d2h),
    .tl_rstmgr_aon_o  (tl_rstmgr_aon_d_h2d),
    .tl_rstmgr_aon_i  (tl_rstmgr_aon_d_d2h),
    .tl_clkmgr_aon_o  (tl_clkmgr_aon_d_h2d),
    .tl_clkmgr_aon_i  (tl_clkmgr_aon_d_d2h),
    .tl_rbox_aon_o    (tl_rbox_aon_d_h2d),
    .tl_rbox_aon_i    (tl_rbox_aon_d_d2h),
    .tl_pwm_aon_o     (tl_pwm_aon_d_h2d),
    .tl_pwm_aon_i     (tl_pwm_aon_d_d2h),
    .tl_pinmux_aon_o  (tl_pinmux_aon_d_h2d),
    .tl_pinmux_aon_i  (tl_pinmux_aon_d_d2h),
    .tl_padctrl_aon_o (tl_padctrl_aon_d_h2d),
    .tl_padctrl_aon_i (tl_padctrl_aon_d_d2h),
    .tl_timer_aon_o   (tl_timer_aon_d_h2d),
    .tl_timer_aon_i   (tl_timer_aon_d_d2h),
    .tl_usbdev_aon_o  (tl_usbdev_aon_d_h2d),
    .tl_usbdev_aon_i  (tl_usbdev_aon_d_d2h),
    .tl_ram_ret_aon_o (tl_ram_ret_aon_d_h2d),
    .tl_ram_ret_aon_i (tl_ram_ret_aon_d_d2h),

    .scanmode_i
  );

  // Pinmux connections
  assign mio_d2p = {
    cio_gpio_gpio_d2p,
    cio_i2c0_sda_d2p,
    cio_i2c0_scl_d2p,
    cio_i2c1_sda_d2p,
    cio_i2c1_scl_d2p,
    cio_i2c2_sda_d2p,
    cio_i2c2_scl_d2p,
    cio_uart1_tx_d2p,
    cio_uart2_tx_d2p,
    cio_uart3_tx_d2p
  };
  assign mio_d2p_en = {
    cio_gpio_gpio_en_d2p,
    cio_i2c0_sda_en_d2p,
    cio_i2c0_scl_en_d2p,
    cio_i2c1_sda_en_d2p,
    cio_i2c1_scl_en_d2p,
    cio_i2c2_sda_en_d2p,
    cio_i2c2_scl_en_d2p,
    cio_uart1_tx_en_d2p,
    cio_uart2_tx_en_d2p,
    cio_uart3_tx_en_d2p
  };
  assign {
    cio_gpio_gpio_p2d,
    cio_i2c0_sda_p2d,
    cio_i2c0_scl_p2d,
    cio_i2c1_sda_p2d,
    cio_i2c1_scl_p2d,
    cio_i2c2_sda_p2d,
    cio_i2c2_scl_p2d,
    cio_uart1_rx_p2d,
    cio_uart2_rx_p2d,
    cio_uart3_rx_p2d
  } = mio_p2d;

  // Dedicated IO connections
  // Input-only DIOs have no d2p signals
  assign dio_d2p = {
    1'b0, // DIO28: cio_spi_device_sck
    1'b0, // DIO27: cio_spi_device_csb
    1'b0, // DIO26: cio_spi_device_mosi
    cio_spi_device_miso_d2p, // DIO25
    1'b0, // DIO24: cio_uart_rx
    cio_uart_tx_d2p, // DIO23
    1'b0, // DIO22: cio_usbdev_aon_sense
    cio_usbdev_aon_se0_d2p, // DIO21
    cio_usbdev_aon_dp_pullup_d2p, // DIO20
    cio_usbdev_aon_dn_pullup_d2p, // DIO19
    cio_usbdev_aon_tx_mode_se_d2p, // DIO18
    cio_usbdev_aon_suspend_d2p, // DIO17
    cio_usbdev_aon_d_d2p, // DIO16
    cio_usbdev_aon_dp_d2p, // DIO15
    cio_usbdev_aon_dn_d2p, // DIO14
    1'b0, // DIO13: cio_rbox_aon_ac_present
    1'b0, // DIO12: cio_rbox_aon_ec_entering_rw
    1'b0, // DIO11: cio_rbox_aon_key0_in
    1'b0, // DIO10: cio_rbox_aon_key1_in
    1'b0, // DIO9: cio_rbox_aon_key2_in
    1'b0, // DIO8: cio_rbox_aon_pwrb_in
    cio_rbox_aon_bat_en_d2p, // DIO7
    cio_rbox_aon_ec_in_rw_d2p, // DIO6
    cio_rbox_aon_ec_rst_l_d2p, // DIO5
    cio_rbox_aon_flash_wp_l_d2p, // DIO4
    cio_rbox_aon_key0_out_d2p, // DIO3
    cio_rbox_aon_key1_out_d2p, // DIO2
    cio_rbox_aon_key2_out_d2p, // DIO1
    cio_rbox_aon_pwrb_out_d2p // DIO0
  };

  assign dio_d2p_en = {
    1'b0, // DIO28: cio_spi_device_sck
    1'b0, // DIO27: cio_spi_device_csb
    1'b0, // DIO26: cio_spi_device_mosi
    cio_spi_device_miso_en_d2p, // DIO25
    1'b0, // DIO24: cio_uart_rx
    cio_uart_tx_en_d2p, // DIO23
    1'b0, // DIO22: cio_usbdev_aon_sense
    cio_usbdev_aon_se0_en_d2p, // DIO21
    cio_usbdev_aon_dp_pullup_en_d2p, // DIO20
    cio_usbdev_aon_dn_pullup_en_d2p, // DIO19
    cio_usbdev_aon_tx_mode_se_en_d2p, // DIO18
    cio_usbdev_aon_suspend_en_d2p, // DIO17
    cio_usbdev_aon_d_en_d2p, // DIO16
    cio_usbdev_aon_dp_en_d2p, // DIO15
    cio_usbdev_aon_dn_en_d2p, // DIO14
    1'b0, // DIO13: cio_rbox_aon_ac_present
    1'b0, // DIO12: cio_rbox_aon_ec_entering_rw
    1'b0, // DIO11: cio_rbox_aon_key0_in
    1'b0, // DIO10: cio_rbox_aon_key1_in
    1'b0, // DIO9: cio_rbox_aon_key2_in
    1'b0, // DIO8: cio_rbox_aon_pwrb_in
    cio_rbox_aon_bat_en_en_d2p, // DIO7
    cio_rbox_aon_ec_in_rw_en_d2p, // DIO6
    cio_rbox_aon_ec_rst_l_en_d2p, // DIO5
    cio_rbox_aon_flash_wp_l_en_d2p, // DIO4
    cio_rbox_aon_key0_out_en_d2p, // DIO3
    cio_rbox_aon_key1_out_en_d2p, // DIO2
    cio_rbox_aon_key2_out_en_d2p, // DIO1
    cio_rbox_aon_pwrb_out_en_d2p // DIO0
  };

  // Output-only DIOs have no p2d signal
  assign cio_spi_device_sck_p2d          = dio_p2d[28]; // DIO28
  assign cio_spi_device_csb_p2d          = dio_p2d[27]; // DIO27
  assign cio_spi_device_mosi_p2d         = dio_p2d[26]; // DIO26
  // DIO25: cio_spi_device_miso
  assign cio_uart_rx_p2d                 = dio_p2d[24]; // DIO24
  // DIO23: cio_uart_tx
  assign cio_usbdev_aon_sense_p2d        = dio_p2d[22]; // DIO22
  // DIO21: cio_usbdev_aon_se0
  // DIO20: cio_usbdev_aon_dp_pullup
  // DIO19: cio_usbdev_aon_dn_pullup
  // DIO18: cio_usbdev_aon_tx_mode_se
  // DIO17: cio_usbdev_aon_suspend
  assign cio_usbdev_aon_d_p2d            = dio_p2d[16]; // DIO16
  assign cio_usbdev_aon_dp_p2d           = dio_p2d[15]; // DIO15
  assign cio_usbdev_aon_dn_p2d           = dio_p2d[14]; // DIO14
  assign cio_rbox_aon_ac_present_p2d     = dio_p2d[13]; // DIO13
  assign cio_rbox_aon_ec_entering_rw_p2d = dio_p2d[12]; // DIO12
  assign cio_rbox_aon_key0_in_p2d        = dio_p2d[11]; // DIO11
  assign cio_rbox_aon_key1_in_p2d        = dio_p2d[10]; // DIO10
  assign cio_rbox_aon_key2_in_p2d        = dio_p2d[9]; // DIO9
  assign cio_rbox_aon_pwrb_in_p2d        = dio_p2d[8]; // DIO8
  // DIO7: cio_rbox_aon_bat_en
  // DIO6: cio_rbox_aon_ec_in_rw
  // DIO5: cio_rbox_aon_ec_rst_l
  // DIO4: cio_rbox_aon_flash_wp_l
  // DIO3: cio_rbox_aon_key0_out
  // DIO2: cio_rbox_aon_key1_out
  // DIO1: cio_rbox_aon_key2_out
  // DIO0: cio_rbox_aon_pwrb_out

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
