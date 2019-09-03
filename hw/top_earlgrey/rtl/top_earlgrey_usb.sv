// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_usb #(
  parameter N_USB = 1,
  parameter MAX_USB = 2,
  parameter USB_UART = 1,
  parameter USB_DEVICE = 0
) (
  // Clock and Reset
  input         clk_i,
  input         rst_ni,

  // JTAG interface
  input         jtag_tck_i,
  input         jtag_tms_i,
  input         jtag_trst_ni,
  input         jtag_td_i,
  output        jtag_td_o,

  // UART interface
  input         cio_uart_rx_p2d_i,
  output        cio_uart_tx_d2p_o,
  output        cio_uart_tx_en_d2p_o,

  // USB interface
  input         clk_48mhz_i,
  input         cio_usb_dp_i[MAX_USB],
  output logic  cio_usb_dp_o[MAX_USB],
  output logic  cio_usb_dp_en_o[MAX_USB],

  input         cio_usb_dn_i[MAX_USB],
  output logic  cio_usb_dn_o[MAX_USB],
  output logic  cio_usb_dn_en_o[MAX_USB],

  input         cio_usb_sense_i[MAX_USB],

  output logic  cio_usb_pullup_o[MAX_USB],
  output logic  cio_usb_pullup_en_o[MAX_USB],

  // GPIO x 16 interface
  input [31:0]  cio_gpio_p2d_i,
  output [31:0] cio_gpio_d2p_o,
  output [31:0] cio_gpio_en_d2p_o,

  // SPI Interface (Device)
  input         cio_spi_device_sck_i,
  input         cio_spi_device_csb_i,
  input         cio_spi_device_mosi_i,
  output        cio_spi_device_miso_o,
  output        cio_spi_device_miso_en_o,

  input         scanmode_i  // 1 for Scan
);

  import tlul_pkg::*;
  import top_pkg::*;
  import tl_main_pkg::*;

  tl_h2d_t   tl_h_h2d [N_HOST];
  tl_d2h_t   tl_h_d2h [N_HOST];

  tl_h2d_t   tl_d_h2d [N_DEVICE];
  tl_d2h_t   tl_d_d2h [N_DEVICE];


  logic [63:0]  intr_vector;
  logic         irq_req;
  logic [4:0]   irq_rid;
  logic         irq_ack;
  logic [4:0]   irq_aid;

  // Non-debug module reset == reset for everything except for the debug module
  // and the logic required to access it.
  logic ndmreset_n;
  logic ndmreset_from_dm;
  assign ndmreset_n = (scanmode_i) ? rst_ni : ~ndmreset_from_dm & rst_ni;

  logic debug_req;

  // processor core
  rv_core_ibex #(
    .MHPMCounterNum       (8),
    .MHPMCounterWidth     (40),
    .RV32E                (0),
    .RV32M                (1),
    .DmHaltAddr           (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr      (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress)
  ) core (
    // clock and reset
    .clk_i                (clk_i),
    .rst_ni               (ndmreset_n),
    .test_en_i            (1'b0),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_RAM_MAIN + 'h1000),  // no ROM for now, straight out of SRAM
    // TL-UL buses
    .tl_i_o               (tl_h_h2d[TlCorei]),
    .tl_i_i               (tl_h_d2h[TlCorei]),
    .tl_d_o               (tl_h_h2d[TlCored]),
    .tl_d_i               (tl_h_d2h[TlCored]),
    // interrupts
    .irq_i                (irq_req),//in           // level sensitive IR lines
    .irq_id_i             (irq_rid),//in  [4:0]
    .irq_ack_o            (irq_ack),//out          // irq ack
    .irq_id_o             (irq_aid),//out [4:0]
    // debug interface
    .debug_req_i          (debug_req),
    // CPU control signals
    .fetch_enable_i       (1'b1)
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_rsp;
  logic dmi_req_valid, dmi_req_ready;
  logic dmi_rsp_valid, dmi_rsp_ready;
  logic dmi_rst_n;

  rv_dm #(
    .NrHarts      (  1)
  ) u_dm_top (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .testmode_i    (1'b0),
    .ndmreset_o    (ndmreset_from_dm),
    .dmactive_o    (),
    .debug_req_o   (debug_req),
    .unavailable_i (1'b0),

    // bus device with debug memory (for execution-based debug)
    .tl_d_i        (tl_d_h2d[TlDebugMem]),
    .tl_d_o        (tl_d_d2h[TlDebugMem]),

    // bus host (for system bus accesses, SBA)
    .tl_h_o        (tl_h_h2d[TlDmSba]),
    .tl_h_i        (tl_h_d2h[TlDmSba]),

    // Connection to DTM - compatible to RocketChip Debug Module
    .dmi_rst_ni       (dmi_rst_n),
    .dmi_req_valid_i  (dmi_req_valid),
    .dmi_req_ready_o  (dmi_req_ready),
    .dmi_req_i        (dmi_req      ),

    .dmi_resp_valid_o (dmi_rsp_valid),
    .dmi_resp_ready_i (dmi_rsp_ready),
    .dmi_resp_o       (dmi_rsp      )
  );

  dmi_jtag #(
    .IdcodeValue (32'h00000001) // Temporary value
                                // xxxx             version
                                // xxxxxxxxxxxxxxxx part number
                                // xxxxxxxxxxx      manufacturer id
                                // 1                required by standard
  ) dap (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .testmode_i       (1'b0),

    .dmi_rst_no       (dmi_rst_n),
    .dmi_req_o        (dmi_req),
    .dmi_req_valid_o  (dmi_req_valid),
    .dmi_req_ready_i  (dmi_req_ready),

    .dmi_resp_i       (dmi_rsp      ),
    .dmi_resp_ready_o (dmi_rsp_ready),
    .dmi_resp_valid_i (dmi_rsp_valid),

    //JTAG
    .tck_i            (jtag_tck_i),
    .tms_i            (jtag_tms_i),
    .trst_ni          (jtag_trst_ni),
    .td_i             (jtag_td_i),
    .td_o             (jtag_td_o),
    .tdo_oe_o         (       )
  );

  // sram device
  logic        req;
  logic        we;
  logic [13:0] addr;
  logic [31:0] wdata;
  logic [31:0] wmask;
  logic [31:0] rdata;
  logic        rvalid;

  tlul_adapter_sram #(
    .SramAw(14),
    .SramDw(32),
    .Outstanding(1)
  ) tl_adapter (
    .clk_i,
    .rst_ni   (ndmreset_n),

    .tl_i     (tl_d_h2d[TlRamMain]),
    .tl_o     (tl_d_d2h[TlRamMain]),

    .req_o    (req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (we),
    .addr_o   (addr),
    .wdata_o  (wdata),
    .wmask_o  (wmask),
    .rdata_i  (rdata),
    .rvalid_i (rvalid),
    .rerror_i (2'b00)
    );

  prim_ram_1p #(
    .Width(32),
    .Depth(64 * 1024 / 4) // 64 kB
  ) u_ram (
    .clk_i,
    .rst_ni   (ndmreset_n),

    .req_i    (req),
    .write_i  (we),
    .addr_i   (addr),
    .wdata_i  (wdata),
    .wmask_i  (wmask),
    .rvalid_o (rvalid),
    .rdata_o  (rdata));


  // UART

  logic   intr_uart_tx_watermark, intr_uart_rx_watermark;
  logic   intr_uart_tx_overflow,  intr_uart_rx_overflow;
  logic   intr_uart_rx_frame_err, intr_uart_rx_break_err;
  logic   intr_uart_rx_timeout,   intr_uart_rx_parity_err;

  if (USB_UART == 0) begin : gen_uart
    uart uart (
      .clk_i                (clk_i),
      .rst_ni               (ndmreset_n),
      .tl_i                 (tl_d_h2d[TlUart]),
      .tl_o                 (tl_d_d2h[TlUart]),
      .cio_rx_i             (cio_uart_rx_p2d_i),
      .cio_tx_o             (cio_uart_tx_d2p_o),
      .cio_tx_en_o          (cio_uart_tx_en_d2p_o),
      .intr_tx_watermark_o  (intr_uart_tx_watermark),
      .intr_rx_watermark_o  (intr_uart_rx_watermark),
      .intr_tx_overflow_o   (intr_uart_tx_overflow),
      .intr_rx_overflow_o   (intr_uart_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart_rx_break_err),
      .intr_rx_timeout_o    (intr_uart_rx_timeout),
      .intr_rx_parity_err_o (intr_uart_rx_parity_err)
    );

  end else begin : gen_uuart
    logic unused_rx = cio_uart_rx_p2d_i;
    assign cio_uart_tx_d2p_o = 0;
    assign cio_uart_tx_en_d2p_o = 0;

    usbuart uart (
      .clk_i                (clk_i),
      .clk_48mhz_i          (clk_48mhz_i),
      .rst_ni               (ndmreset_n),
      .tl_i                 (tl_d_h2d[TlUart]),
      .tl_o                 (tl_d_d2h[TlUart]),
      .cio_usb_dp_i         (cio_usb_dp_i[USB_UART - 1]),
      .cio_usb_dp_o         (cio_usb_dp_o[USB_UART - 1]),
      .cio_usb_dp_en_o      (cio_usb_dp_en_o[USB_UART - 1]),
      .cio_usb_dn_i         (cio_usb_dn_i[USB_UART - 1]),
      .cio_usb_dn_o         (cio_usb_dn_o[USB_UART - 1]),
      .cio_usb_dn_en_o      (cio_usb_dn_en_o[USB_UART - 1]),
      .cio_usb_sense_i      (cio_usb_sense_i[USB_UART - 1]),
      .cio_pullup_o         (cio_usb_pullup_o[USB_UART - 1]),
      .cio_pullup_en_o      (cio_usb_pullup_en_o[USB_UART - 1]),

      .intr_tx_watermark_o  (intr_uart_tx_watermark),
      .intr_rx_watermark_o  (intr_uart_rx_watermark),
      .intr_tx_overflow_o   (intr_uart_tx_overflow),
      .intr_rx_overflow_o   (intr_uart_rx_overflow),
      .intr_rx_frame_err_o  (intr_uart_rx_frame_err),
      .intr_rx_break_err_o  (intr_uart_rx_break_err),
      .intr_rx_timeout_o    (intr_uart_rx_timeout),
      .intr_rx_parity_err_o (intr_uart_rx_parity_err)
    );
  end // block: gen_uuart

  // GPIO

  logic   [31:0]  intr_gpio;

  gpio gpio (
    .clk_i                (clk_i),
    .rst_ni               (ndmreset_n),
    .tl_i                 (tl_d_h2d[TlGpio]),
    .tl_o                 (tl_d_d2h[TlGpio]),
    .cio_gpio_i           (cio_gpio_p2d_i),
    .cio_gpio_o           (cio_gpio_d2p_o),
    .cio_gpio_en_o        (cio_gpio_en_d2p_o),
    .intr_gpio_o          (intr_gpio)
  );

  // SPI Device instance
  logic intr_spi_device_rxne, intr_spi_device_rxlvl, intr_spi_device_rxerr;
  logic intr_spi_device_txe, intr_spi_device_txf;

  if (USB_DEVICE == 0) begin : gen_spi
    spi_device spi_device (
      .clk_i,
      .rst_ni         (ndmreset_n),

      .tl_i           (tl_d_h2d[TlSpiDevice]),
      .tl_o           (tl_d_d2h[TlSpiDevice]),

      .cio_sck_i      (cio_spi_device_sck_i),
      .cio_csb_i      (cio_spi_device_csb_i),
      .cio_mosi_i     (cio_spi_device_mosi_i),
      .cio_miso_o     (cio_spi_device_miso_o),
      .cio_miso_en_o  (cio_spi_device_miso_en_o),

      .intr_rxne_o    (intr_spi_device_rxne),
      .intr_rxlvl_o   (intr_spi_device_rxlvl),
      .intr_txe_o     (intr_spi_device_txe),
      .intr_txf_o     (intr_spi_device_txf),
      .intr_rxerr_o   (intr_spi_device_rxerr),
      .intr_txlvl_o   ()
    );
  end else begin : gen_usbdev // block: gen_spi
    logic unused_sck = cio_spi_device_sck_i;
    logic unused_csb = cio_spi_device_csb_i;
    logic unused_mosi = cio_spi_device_mosi_i;

    assign intr_spi_device_rxlvl = 0;
    assign intr_spi_device_txf = 0;
    assign cio_spi_device_miso_o = 0;
    assign cio_spi_device_miso_en_o = 0;

    usbdev udev (
      .clk_i                (clk_i),
      .clk_usb_48mhz_i      (clk_48mhz_i),
      .rst_ni               (ndmreset_n),
      .tl_d_i               (tl_d_h2d[TlSpiDevice]),
      .tl_d_o               (tl_d_d2h[TlSpiDevice]),
      .cio_usb_dp_i         (cio_usb_dp_i[USB_DEVICE - 1]),
      .cio_usb_dp_o         (cio_usb_dp_o[USB_DEVICE - 1]),
      .cio_usb_dp_en_o      (cio_usb_dp_en_o[USB_DEVICE - 1]),
      .cio_usb_dn_i         (cio_usb_dn_i[USB_DEVICE - 1]),
      .cio_usb_dn_o         (cio_usb_dn_o[USB_DEVICE - 1]),
      .cio_usb_dn_en_o      (cio_usb_dn_en_o[USB_DEVICE - 1]),
      .cio_usb_sense_i      (cio_usb_sense_i[USB_DEVICE - 1]),
      .cio_usb_pullup_o     (cio_usb_pullup_o[USB_DEVICE - 1]),
      .cio_usb_pullup_en_o  (cio_usb_pullup_en_o[USB_DEVICE - 1]),

      .intr_pkt_received_o  (intr_spi_device_rxne),
      .intr_pkt_sent_o      (intr_spi_device_txe),
      .intr_disconnected_o  (),
      .intr_host_lost_o     (),
      .intr_link_reset_o    (),
      .intr_link_suspend_o  (),
      .intr_link_resume_o   (),
      .intr_av_empty_o      (intr_spi_device_rxlvl),
      .intr_rx_full_o       (intr_spi_device_rxerr),
      .intr_av_overflow_o   (intr_spi_device_txf)
    );
  end // block: gen_usbdev

  // interrupt assignments

  assign intr_vector = {
      35'h0,
      intr_spi_device_rxne,
      intr_spi_device_rxlvl,
      intr_spi_device_txe,
      intr_spi_device_txf,
      intr_spi_device_rxerr,
      intr_uart_tx_watermark,
      intr_uart_rx_watermark,
      intr_uart_tx_overflow,
      intr_uart_rx_overflow,
      intr_uart_rx_frame_err,
      intr_uart_rx_break_err,
      intr_uart_rx_timeout,
      intr_uart_rx_parity_err,
      intr_gpio[15:0]
  };

  // TODO: Connect Interrupt controller
  assign irq_req = intr_gpio[15];
  assign irq_rid = 'd15;


  // TL-UL Crossbar
  tlul_xbar_usb u_xbar (
    .clk_i  (clk_i),
    .rst_ni (ndmreset_n),

    .tl_h_i (tl_h_h2d),
    .tl_h_o (tl_h_d2h),

    .tl_d_o (tl_d_h2d),
    .tl_d_i (tl_d_d2h)
  );

  // Tie off unused USB
  if (N_USB < MAX_USB) begin: gen_utie
    for (genvar j = N_USB; j < MAX_USB; j = j + 1) begin
      logic unused_usb;
      assign unused_usb = cio_usb_dp_i[j] | cio_usb_dn_i[j] | cio_usb_sense_i[j];
      assign cio_usb_dp_o[j] = 1'b0;
      assign cio_usb_dp_en_o[j] = 1'b0;
      assign cio_usb_dn_o[j] = 1'b0;
      assign cio_usb_dn_en_o[j] = 1'b0;
      assign cio_usb_pullup_o[j] = 1'b0;
      assign cio_usb_pullup_en_o[j] = 1'b0;
    end
  end // block: gen_utie

endmodule
