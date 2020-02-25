// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey #(
  parameter bit IbexPipeLine = 0
) (
  // Clock and Reset
  input               clk_i,
  input               rst_ni,

  // USB clock
  input               clk_usb_48mhz_i,

  // JTAG interface
  input               jtag_tck_i,
  input               jtag_tms_i,
  input               jtag_trst_ni,
  input               jtag_td_i,
  output              jtag_td_o,

  // Multiplexed I/O
  input        [31:0] mio_in_i,
  output logic [31:0] mio_out_o,
  output logic [31:0] mio_oe_o,

  // Dedicated I/O
  input               dio_spi_device_sck_i,
  input               dio_spi_device_csb_i,
  input               dio_spi_device_mosi_i,
  output logic        dio_spi_device_miso_o,
  output logic        dio_spi_device_miso_en_o,
  input               dio_uart_rx_i,
  output logic        dio_uart_tx_o,
  output logic        dio_uart_tx_en_o,
  input               dio_usbdev_sense_i,
  output logic        dio_usbdev_pullup_o,
  output logic        dio_usbdev_pullup_en_o,
  input               dio_usbdev_dp_i,
  output logic        dio_usbdev_dp_o,
  output logic        dio_usbdev_dp_en_o,
  input               dio_usbdev_dn_i,
  output logic        dio_usbdev_dn_o,
  output logic        dio_usbdev_dn_en_o,

  input               scanmode_i  // 1 for Scan
);

  // JTAG IDCODE for development versions of this code.
  // Manufacturers of OpenTitan chips must replace this code with one of their
  // own IDs.
  // Field structure as defined in the IEEE 1149.1 (JTAG) specification,
  // section 12.1.1.
  localparam JTAG_IDCODE = {
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
  tl_h2d_t  tl_gpio_d_h2d;
  tl_d2h_t  tl_gpio_d_d2h;
  tl_h2d_t  tl_spi_device_d_h2d;
  tl_d2h_t  tl_spi_device_d_d2h;
  tl_h2d_t  tl_flash_ctrl_d_h2d;
  tl_d2h_t  tl_flash_ctrl_d_d2h;
  tl_h2d_t  tl_rv_timer_d_h2d;
  tl_d2h_t  tl_rv_timer_d_d2h;
  tl_h2d_t  tl_aes_d_h2d;
  tl_d2h_t  tl_aes_d_d2h;
  tl_h2d_t  tl_hmac_d_h2d;
  tl_d2h_t  tl_hmac_d_d2h;
  tl_h2d_t  tl_rv_plic_d_h2d;
  tl_d2h_t  tl_rv_plic_d_d2h;
  tl_h2d_t  tl_pinmux_d_h2d;
  tl_d2h_t  tl_pinmux_d_d2h;
  tl_h2d_t  tl_alert_handler_d_h2d;
  tl_d2h_t  tl_alert_handler_d_d2h;
  tl_h2d_t  tl_nmi_gen_d_h2d;
  tl_d2h_t  tl_nmi_gen_d_d2h;
  tl_h2d_t  tl_usbdev_d_h2d;
  tl_d2h_t  tl_usbdev_d_d2h;

  tl_h2d_t tl_rom_d_h2d;
  tl_d2h_t tl_rom_d_d2h;
  tl_h2d_t tl_ram_main_d_h2d;
  tl_d2h_t tl_ram_main_d_d2h;
  tl_h2d_t tl_eflash_d_h2d;
  tl_d2h_t tl_eflash_d_d2h;

  tl_h2d_t tl_main_h_h2d;
  tl_d2h_t tl_main_h_d2h;
  tl_h2d_t tl_peri_d_h2d;
  tl_d2h_t tl_peri_d_d2h;

  assign tl_main_h_h2d = tl_peri_d_h2d;
  assign tl_peri_d_d2h = tl_main_h_d2h;

  //reset wires declaration
  logic lc_rst_n;
  logic sys_rst_n;
  logic sys_fixed_rst_n;
  logic spi_device_rst_n;
  logic usb_rst_n;

  //clock wires declaration
  logic main_clk;
  logic fixed_clk;
  logic usb_clk;

  // Signals
  logic [31:0] m2p;
  logic [31:0] p2m;
  logic [31:0] p2m_en;
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
  logic        cio_spi_device_mosi_p2d;
  logic        cio_spi_device_miso_d2p;
  logic        cio_spi_device_miso_en_d2p;
  // flash_ctrl
  // rv_timer
  // aes
  // hmac
  // rv_plic
  // pinmux
  // alert_handler
  // nmi_gen
  // usbdev
  logic        cio_usbdev_sense_p2d;
  logic        cio_usbdev_dp_p2d;
  logic        cio_usbdev_dn_p2d;
  logic        cio_usbdev_pullup_d2p;
  logic        cio_usbdev_pullup_en_d2p;
  logic        cio_usbdev_dp_d2p;
  logic        cio_usbdev_dp_en_d2p;
  logic        cio_usbdev_dn_d2p;
  logic        cio_usbdev_dn_en_d2p;


  logic [78:0]  intr_vector;
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
  logic intr_flash_ctrl_prog_empty;
  logic intr_flash_ctrl_prog_lvl;
  logic intr_flash_ctrl_rd_full;
  logic intr_flash_ctrl_rd_lvl;
  logic intr_flash_ctrl_op_done;
  logic intr_flash_ctrl_op_error;
  logic intr_rv_timer_timer_expired_0_0;
  logic intr_hmac_hmac_done;
  logic intr_hmac_fifo_full;
  logic intr_hmac_hmac_err;
  logic intr_alert_handler_classa;
  logic intr_alert_handler_classb;
  logic intr_alert_handler_classc;
  logic intr_alert_handler_classd;
  logic intr_nmi_gen_esc0;
  logic intr_nmi_gen_esc1;
  logic intr_nmi_gen_esc2;
  logic intr_nmi_gen_esc3;
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


  
  logic [0:0] irq_plic;
  logic [0:0] msip;
  logic [6:0] irq_id[1];
  logic [6:0] unused_irq_id[1];

  // this avoids lint errors
  assign unused_irq_id = irq_id;

  // Alert list
  prim_pkg::alert_tx_t [alert_pkg::NAlerts-1:0]  alert_tx;
  prim_pkg::alert_rx_t [alert_pkg::NAlerts-1:0]  alert_rx;
  // Escalation outputs
  prim_pkg::esc_tx_t [alert_pkg::N_ESC_SEV-1:0]  esc_tx;
  prim_pkg::esc_rx_t [alert_pkg::N_ESC_SEV-1:0]  esc_rx;


  // Clock assignments
  assign main_clk = clk_i;
  assign fixed_clk = clk_i;

  // Separate clock input for USB clock
  assign usb_clk = clk_usb_48mhz_i;

  // Non-debug module reset == reset for everything except for the debug module
  logic ndmreset_req;

  // root resets
  // TODO: lc_rst_n is not the true root reset.  It will be differentiated once the
  //       the reset controller logic is present
  assign lc_rst_n = rst_ni;
  assign sys_rst_n = (scanmode_i) ? lc_rst_n : ~ndmreset_req & lc_rst_n;

  // Non-root reset assignments
  assign sys_fixed_rst_n = sys_rst_n;
  assign spi_device_rst_n = sys_rst_n;

  // Reset synchronizer for USB
  logic [1:0] usb_rst_q;
  always_ff @(posedge usb_clk) begin
    usb_rst_q <= {usb_rst_q[0], sys_rst_n};
  end
  assign usb_rst_n = sys_rst_n & usb_rst_q[1];

  // debug request from rv_dm to core
  logic debug_req;

  // processor core
  rv_core_ibex #(
    .PMPEnable           (0),
    .PMPGranularity      (0),
    .PMPNumRegions       (4),
    .MHPMCounterNum      (8),
    .MHPMCounterWidth    (40),
    .RV32E               (0),
    .RV32M               (1),
    .DbgTriggerEn        (1),
    .DmHaltAddr          (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr     (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress),
    .PipeLine            (IbexPipeLine)
  ) core (
    // clock and reset
    .clk_i                (main_clk),
    .rst_ni               (sys_rst_n),
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
    .core_sleep_o         ()
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  rv_dm #(
    .NrHarts     (1),
    .IdcodeValue (JTAG_IDCODE)
  ) u_dm_top (
    .clk_i         (main_clk),
    .rst_ni        (lc_rst_n),
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
    .td_i             (jtag_td_i),
    .td_o             (jtag_td_o),
    .tdo_oe_o         (       )
  );

  // ROM device
  logic        rom_req;
  logic [11:0] rom_addr;
  logic [31:0] rom_rdata;
  logic        rom_rvalid;

  tlul_adapter_sram #(
    .SramAw(12),
    .SramDw(32),
    .Outstanding(1),
    .ErrOnWrite(1)
  ) tl_adapter_rom (
    .clk_i   (main_clk),
    .rst_ni   (sys_rst_n),

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

  prim_rom #(
    .Width(32),
    .Depth(4096)
  ) u_rom_rom (
    .clk_i   (main_clk),
    .rst_ni   (sys_rst_n),
    .cs_i     (rom_req),
    .addr_i   (rom_addr),
    .dout_o   (rom_rdata),
    .dvalid_o (rom_rvalid)
  );

  // sram device
  logic        ram_main_req;
  logic        ram_main_we;
  logic [13:0] ram_main_addr;
  logic [31:0] ram_main_wdata;
  logic [31:0] ram_main_wmask;
  logic [31:0] ram_main_rdata;
  logic        ram_main_rvalid;

  tlul_adapter_sram #(
    .SramAw(14),
    .SramDw(32),
    .Outstanding(1)
  ) tl_adapter_ram_main (
    .clk_i   (main_clk),
    .rst_ni   (sys_rst_n),
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
    .rerror_i (2'b00)
  );

  prim_ram_1p #(
    .Width(32),
    .Depth(16384),
    .DataBitsPerMask(8)
  ) u_ram1p_ram_main (
    .clk_i   (main_clk),
    .rst_ni   (sys_rst_n),

    .req_i    (ram_main_req),
    .write_i  (ram_main_we),
    .addr_i   (ram_main_addr),
    .wdata_i  (ram_main_wdata),
    .wmask_i  (ram_main_wmask),
    .rvalid_o (ram_main_rvalid),
    .rdata_o  (ram_main_rdata)
  );

  // define inter-module signals
  flash_ctrl_pkg::flash_req_t flash_ctrl_eflash_flash_req;
  flash_ctrl_pkg::flash_rsp_t flash_ctrl_eflash_flash_rsp;

  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic [FLASH_DW-1:0] flash_host_rdata;
  logic [FLASH_AW-1:0] flash_host_addr;

  tlul_adapter_sram #(
    .SramAw(FLASH_AW),
    .SramDw(FLASH_DW),
    .Outstanding(1),
    .ByteAccess(0),
    .ErrOnWrite(1)
  ) tl_adapter_eflash (
    .clk_i   (main_clk),
    .rst_ni   (lc_rst_n),

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

  flash_phy #(
    .NumBanks(FLASH_BANKS),
    .PagesPerBank(FLASH_PAGES_PER_BANK),
    .WordsPerPage(FLASH_WORDS_PER_PAGE),
    .DataWidth(32)
  ) u_flash_eflash (
    .clk_i   (main_clk),
    .rst_ni   (lc_rst_n),
    .host_req_i      (flash_host_req),
    .host_addr_i     (flash_host_addr),
    .host_req_rdy_o  (flash_host_req_rdy),
    .host_req_done_o (flash_host_req_done),
    .host_rdata_o    (flash_host_rdata),
    .flash_ctrl_i    (flash_ctrl_eflash_flash_req),
    .flash_ctrl_o    (flash_ctrl_eflash_flash_rsp)
  );



  uart uart (
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

      .clk_i (fixed_clk),
      .rst_ni (sys_fixed_rst_n)
  );

  gpio gpio (
      .tl_i (tl_gpio_d_h2d),
      .tl_o (tl_gpio_d_d2h),

      // Input
      .cio_gpio_i    (cio_gpio_gpio_p2d),

      // Output
      .cio_gpio_o    (cio_gpio_gpio_d2p),
      .cio_gpio_en_o (cio_gpio_gpio_en_d2p),

      // Interrupt
      .intr_gpio_o (intr_gpio_gpio),

      .clk_i (fixed_clk),
      .rst_ni (sys_fixed_rst_n)
  );

  spi_device spi_device (
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

      .clk_i (fixed_clk),
      .rst_ni (spi_device_rst_n)
  );

  flash_ctrl flash_ctrl (
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
      .flash_o(flash_ctrl_eflash_flash_req),
      .flash_i(flash_ctrl_eflash_flash_rsp),

      .clk_i (main_clk),
      .rst_ni (lc_rst_n)
  );

  rv_timer rv_timer (
      .tl_i (tl_rv_timer_d_h2d),
      .tl_o (tl_rv_timer_d_d2h),

      // Interrupt
      .intr_timer_expired_0_0_o (intr_rv_timer_timer_expired_0_0),

      .clk_i (fixed_clk),
      .rst_ni (sys_fixed_rst_n)
  );

  aes aes (
      .tl_i (tl_aes_d_h2d),
      .tl_o (tl_aes_d_d2h),

      .clk_i (main_clk),
      .rst_ni (sys_rst_n)
  );

  hmac hmac (
      .tl_i (tl_hmac_d_h2d),
      .tl_o (tl_hmac_d_d2h),

      // Interrupt
      .intr_hmac_done_o (intr_hmac_hmac_done),
      .intr_fifo_full_o (intr_hmac_fifo_full),
      .intr_hmac_err_o  (intr_hmac_hmac_err),
      
      // [0]: msg_push_sha_disabled 
      .alert_tx_o  ( alert_tx[0:0] ),
      .alert_rx_i  ( alert_rx[0:0] ),

      .clk_i (main_clk),
      .rst_ni (sys_rst_n)
  );

  rv_plic rv_plic (
      .tl_i (tl_rv_plic_d_h2d),
      .tl_o (tl_rv_plic_d_d2h),

      .intr_src_i (intr_vector),
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),

      .clk_i (main_clk),
      .rst_ni (sys_rst_n)
  );

  pinmux pinmux (
      .tl_i (tl_pinmux_d_h2d),
      .tl_o (tl_pinmux_d_d2h),

      .periph_to_mio_i      (p2m    ),
      .periph_to_mio_oe_i   (p2m_en ),
      .mio_to_periph_o      (m2p    ),

      .mio_out_o            (mio_out_o),
      .mio_oe_o             (mio_oe_o ),
      .mio_in_i             (mio_in_i ),

      .clk_i (main_clk),
      .rst_ni (sys_rst_n)
  );

  alert_handler alert_handler (
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

      .clk_i (main_clk),
      .rst_ni (sys_rst_n)
  );

  nmi_gen nmi_gen (
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

      .clk_i (main_clk),
      .rst_ni (sys_rst_n)
  );

  usbdev usbdev (
      .tl_i (tl_usbdev_d_h2d),
      .tl_o (tl_usbdev_d_d2h),

      // Differential data - Currently not used.
      .cio_d_i          (1'b0),
      .cio_d_o          (),
      .cio_se0_o        (),

      // Single-ended data
      .cio_dp_i         (cio_usbdev_dp_p2d),
      .cio_dn_i         (cio_usbdev_dn_p2d),
      .cio_dp_o         (cio_usbdev_dp_d2p),
      .cio_dn_o         (cio_usbdev_dn_d2p),

      // Non-data I/O
      .cio_sense_i      (cio_usbdev_sense_p2d),
      .cio_oe_o         (cio_usbdev_dp_en_d2p),
      .cio_tx_mode_se_o (),
      .cio_pullup_en_o  (cio_usbdev_pullup_en_d2p),
      .cio_suspend_o    (),

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

      .clk_i (fixed_clk),
      .clk_usb_48mhz_i (usb_clk),
      .rst_ni (sys_fixed_rst_n),
      .rst_usb_48mhz_ni (usb_rst_n)
  );

  // USB assignments
  assign cio_usbdev_dn_en_d2p = cio_usbdev_dp_en_d2p; // have a single output enable only
  assign cio_usbdev_pullup_d2p = 1'b1;

  // interrupt assignments
  assign intr_vector = {
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
      intr_nmi_gen_esc3,
      intr_nmi_gen_esc2,
      intr_nmi_gen_esc1,
      intr_nmi_gen_esc0,
      intr_alert_handler_classd,
      intr_alert_handler_classc,
      intr_alert_handler_classb,
      intr_alert_handler_classa,
      intr_hmac_hmac_err,
      intr_hmac_fifo_full,
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
      intr_gpio_gpio
  };

  // TL-UL Crossbar
  xbar_main u_xbar_main (
    .clk_main_i (main_clk),
    .clk_fixed_i (fixed_clk),
    .rst_main_ni (sys_rst_n),
    .rst_fixed_ni (sys_fixed_rst_n),
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
    .tl_peri_o          (tl_peri_d_h2d),
    .tl_peri_i          (tl_peri_d_d2h),
    .tl_flash_ctrl_o    (tl_flash_ctrl_d_h2d),
    .tl_flash_ctrl_i    (tl_flash_ctrl_d_d2h),
    .tl_hmac_o          (tl_hmac_d_h2d),
    .tl_hmac_i          (tl_hmac_d_d2h),
    .tl_aes_o           (tl_aes_d_h2d),
    .tl_aes_i           (tl_aes_d_d2h),
    .tl_rv_plic_o       (tl_rv_plic_d_h2d),
    .tl_rv_plic_i       (tl_rv_plic_d_d2h),
    .tl_pinmux_o        (tl_pinmux_d_h2d),
    .tl_pinmux_i        (tl_pinmux_d_d2h),
    .tl_alert_handler_o (tl_alert_handler_d_h2d),
    .tl_alert_handler_i (tl_alert_handler_d_d2h),
    .tl_nmi_gen_o       (tl_nmi_gen_d_h2d),
    .tl_nmi_gen_i       (tl_nmi_gen_d_d2h),

    .scanmode_i
  );
  xbar_peri u_xbar_peri (
    .clk_peri_i (fixed_clk),
    .rst_peri_ni (sys_fixed_rst_n),
    .tl_main_i       (tl_main_h_h2d),
    .tl_main_o       (tl_main_h_d2h),
    .tl_uart_o       (tl_uart_d_h2d),
    .tl_uart_i       (tl_uart_d_d2h),
    .tl_gpio_o       (tl_gpio_d_h2d),
    .tl_gpio_i       (tl_gpio_d_d2h),
    .tl_spi_device_o (tl_spi_device_d_h2d),
    .tl_spi_device_i (tl_spi_device_d_d2h),
    .tl_rv_timer_o   (tl_rv_timer_d_h2d),
    .tl_rv_timer_i   (tl_rv_timer_d_d2h),
    .tl_usbdev_o     (tl_usbdev_d_h2d),
    .tl_usbdev_i     (tl_usbdev_d_d2h),

    .scanmode_i
  );

  // Pinmux connections
  assign p2m = {
    cio_gpio_gpio_d2p
  };
  assign p2m_en = {
    cio_gpio_gpio_en_d2p
  };
  assign {
    cio_gpio_gpio_p2d
  } = m2p;

  assign cio_spi_device_sck_p2d   = dio_spi_device_sck_i;
  assign cio_spi_device_csb_p2d   = dio_spi_device_csb_i;
  assign cio_spi_device_mosi_p2d  = dio_spi_device_mosi_i;
  assign dio_spi_device_miso_o    = cio_spi_device_miso_d2p;
  assign dio_spi_device_miso_en_o = cio_spi_device_miso_en_d2p;
  assign cio_uart_rx_p2d          = dio_uart_rx_i;
  assign dio_uart_tx_o            = cio_uart_tx_d2p;
  assign dio_uart_tx_en_o         = cio_uart_tx_en_d2p;
  assign cio_usbdev_sense_p2d     = dio_usbdev_sense_i;
  assign dio_usbdev_pullup_o      = cio_usbdev_pullup_d2p;
  assign dio_usbdev_pullup_en_o   = cio_usbdev_pullup_en_d2p;
  assign cio_usbdev_dp_p2d        = dio_usbdev_dp_i;
  assign dio_usbdev_dp_o          = cio_usbdev_dp_d2p;
  assign dio_usbdev_dp_en_o       = cio_usbdev_dp_en_d2p;
  assign cio_usbdev_dn_p2d        = dio_usbdev_dn_i;
  assign dio_usbdev_dn_o          = cio_usbdev_dn_d2p;
  assign dio_usbdev_dn_en_o       = cio_usbdev_dn_en_d2p;

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
