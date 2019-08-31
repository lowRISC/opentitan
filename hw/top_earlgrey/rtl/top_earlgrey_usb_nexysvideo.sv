// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_usb_nexysvideo (
  // Clock and Reset
  input  IO_CLK,
  input  IO_RST_N,
  // JTAG interface
  input  IO_DPS0, // IO_JTCK,    IO_SDCK
  input  IO_DPS3, // IO_JTMS,    IO_SDCSB
  input  IO_DPS1, // IO_JTDI,    IO_SDMOSI
  input  IO_DPS4, // IO_JTRST_N,
  input  IO_DPS5, // IO_JSRST_N,
  output IO_DPS2, // IO_JTDO,    IO_MISO
  input  IO_DPS6, // JTAG=0,     SPI=1
  // UART interface
  input  IO_URX,
  output IO_UTX,
  // USB interface
  inout  IO_USB_DP0,
  inout  IO_USB_DN0,
  input  IO_USB_SENSE0,
  output IO_USB_PULLUP0,
  inout  IO_USB_DP1,
  inout  IO_USB_DN1,
  input  IO_USB_SENSE1,
  output IO_USB_PULLUP1,
  output IO_OBS,
  // GPIO x 16 interface
  inout  IO_GP0,
  inout  IO_GP1,
  inout  IO_GP2,
  inout  IO_GP3,
  inout  IO_GP4,
  inout  IO_GP5,
  inout  IO_GP6,
  inout  IO_GP7,
  inout  IO_GP8,
  inout  IO_GP9,
  inout  IO_GP10,
  inout  IO_GP11,
  inout  IO_GP12,
  inout  IO_GP13,
  inout  IO_GP14,
  inout  IO_GP15
);

  localparam MAX_USB=2;

  logic        clk_sys, clk_48mhz, rst_sys_n;
  logic [31:0] cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic        cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;
  logic        cio_usb_dp_p2d[MAX_USB], cio_usb_dp_d2p[MAX_USB], cio_usb_dp_en_d2p[MAX_USB];
  logic        cio_usb_dn_p2d[MAX_USB], cio_usb_dn_d2p[MAX_USB], cio_usb_dn_en_d2p[MAX_USB];
  logic        cio_usb_sense_p2d[MAX_USB];
  logic        cio_usb_pullup_d2p[MAX_USB], cio_usb_pullup_en_d2p[MAX_USB];
  logic        cio_spi_device_sck_p2d, cio_spi_device_csb_p2d, cio_spi_device_mosi_p2d;
  logic        cio_spi_device_miso_d2p, cio_spi_device_miso_en_d2p;
  logic        cio_jtag_tck_p2d, cio_jtag_tms_p2d, cio_jtag_tdi_p2d, cio_jtag_tdo_d2p;
  logic        cio_jtag_trst_n_p2d, cio_jtag_srst_n_p2d;

  // Top-level design
  top_earlgrey_usb #(
    .MAX_USB(MAX_USB),
    .N_USB(2),
    .USB_UART(2),
    .USB_DEVICE(1)
  ) top_earlgrey_usb  (
    .clk_i                (clk_sys),
    .rst_ni               (rst_sys_n),

    .jtag_tck_i           (cio_jtag_tck_p2d),
    .jtag_tms_i           (cio_jtag_tms_p2d),
    .jtag_trst_ni         (cio_jtag_trst_n_p2d),
    .jtag_td_i            (cio_jtag_tdi_p2d),
    .jtag_td_o            (cio_jtag_tdo_d2p),

    .cio_uart_rx_p2d_i    (cio_uart_rx_p2d),
    .cio_uart_tx_d2p_o    (cio_uart_tx_d2p),
    .cio_uart_tx_en_d2p_o (cio_uart_tx_en_d2p),
    .clk_48mhz_i          (clk_48mhz),
    .cio_usb_dp_i         (cio_usb_dp_p2d),
    .cio_usb_dp_o         (cio_usb_dp_d2p),
    .cio_usb_dp_en_o      (cio_usb_dp_en_d2p),
    .cio_usb_dn_i         (cio_usb_dn_p2d),
    .cio_usb_dn_o         (cio_usb_dn_d2p),
    .cio_usb_dn_en_o      (cio_usb_dn_en_d2p),
    .cio_usb_sense_i      (cio_usb_sense_p2d),
    .cio_usb_pullup_o     (cio_usb_pullup_d2p),
    .cio_usb_pullup_en_o  (cio_usb_pullup_en_d2p),

    .cio_gpio_p2d_i       (cio_gpio_p2d),
    .cio_gpio_d2p_o       (cio_gpio_d2p),
    .cio_gpio_en_d2p_o    (cio_gpio_en_d2p),

    .cio_spi_device_sck_i     (cio_spi_device_sck_p2d),
    .cio_spi_device_csb_i     (cio_spi_device_csb_p2d),
    .cio_spi_device_mosi_i    (cio_spi_device_mosi_p2d),
    .cio_spi_device_miso_o    (cio_spi_device_miso_d2p),
    .cio_spi_device_miso_en_o (cio_spi_device_miso_en_d2p),

    .scanmode_i               (1'b0)// 1 for Scan
  );

  // Clock and reset
  clkgen_xil7series clkgen (
    .IO_CLK    (IO_CLK),
    .IO_RST_N  (IO_RST_N & cio_jtag_srst_n_p2d),
    .clk_sys   (clk_sys),
    .clk_48MHz (clk_48mhz),
    .rst_sys_n (rst_sys_n)
  );

  assign  IO_OBS = cio_usb_dp_en_d2p[0];
  // pad control
  padctl_usb padctl (
    // UART
    .cio_uart_rx_p2d,
    .cio_uart_tx_d2p,
    .cio_uart_tx_en_d2p,
    // USB
    .cio_usb_dp_p2d(cio_usb_dp_p2d),
    .cio_usb_dp_d2p(cio_usb_dp_d2p),
    .cio_usb_dp_en_d2p(cio_usb_dp_en_d2p),
    .cio_usb_dn_p2d(cio_usb_dn_p2d),
    .cio_usb_dn_d2p(cio_usb_dn_d2p),
    .cio_usb_dn_en_d2p(cio_usb_dn_en_d2p),
    .cio_usb_sense_p2d(cio_usb_sense_p2d),
    .cio_usb_pullup_d2p(cio_usb_pullup_d2p),
    .cio_usb_pullup_en_d2p(cio_usb_pullup_en_d2p),
    // GPIO
    .cio_gpio_p2d,
    .cio_gpio_d2p,
    .cio_gpio_en_d2p,
    // pads
    .IO_URX,
    .IO_UTX,
    .IO_USB_DP0,
    .IO_USB_DN0,
    .IO_USB_SENSE0,
    .IO_USB_PULLUP0,
    .IO_USB_DP1,
    .IO_USB_DN1,
    .IO_USB_SENSE1,
    .IO_USB_PULLUP1,
    .IO_GP0,
    .IO_GP1,
    .IO_GP2,
    .IO_GP3,
    .IO_GP4,
    .IO_GP5,
    .IO_GP6,
    .IO_GP7,
    .IO_GP8,
    .IO_GP9,
    .IO_GP10,
    .IO_GP11,
    .IO_GP12,
    .IO_GP13,
    .IO_GP14,
    .IO_GP15,

    .cio_spi_device_sck_p2d,
    .cio_spi_device_csb_p2d,
    .cio_spi_device_mosi_p2d,
    .cio_spi_device_miso_d2p,
    .cio_spi_device_miso_en_d2p,
    .cio_jtag_tck_p2d,
    .cio_jtag_tms_p2d,
    .cio_jtag_trst_n_p2d,
    .cio_jtag_srst_n_p2d,
    .cio_jtag_tdi_p2d,
    .cio_jtag_tdo_d2p,
    .IO_DPS0,
    .IO_DPS1,
    .IO_DPS2,
    .IO_DPS3,
    .IO_DPS4,
    .IO_DPS5,
    .IO_DPS6
  );
endmodule
