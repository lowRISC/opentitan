// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_nexysvideo (
  // Clock and Reset
  input               IO_CLK,
  input               IO_RST_N,
  // JTAG interface
  input               IO_DPS0, // IO_JTCK,    IO_SDCK
  input               IO_DPS3, // IO_JTMS,    IO_SDCSB
  input               IO_DPS1, // IO_JTDI,    IO_SDMOSI
  input               IO_DPS4, // IO_JTRST_N,
  input               IO_DPS5, // IO_JSRST_N,
  output              IO_DPS2, // IO_JTDO,    IO_MISO
  input               IO_DPS6, // JTAG=0,     SPI=1
  input               IO_DPS7, // BOOTSTRAP=1
  // UART interface
  input               IO_URX,
  output              IO_UTX,
  // USB interface
  inout               IO_USB_DP0,
  inout               IO_USB_DN0,
  input               IO_USB_SENSE0,
  output              IO_USB_PULLUP0,
  // GPIO x 16 interface
  inout               IO_GP0,
  inout               IO_GP1,
  inout               IO_GP2,
  inout               IO_GP3,
  inout               IO_GP4,
  inout               IO_GP5,
  inout               IO_GP6,
  inout               IO_GP7,
  inout               IO_GP8,
  inout               IO_GP9,
  inout               IO_GP10,
  inout               IO_GP11,
  inout               IO_GP12,
  inout               IO_GP13,
  inout               IO_GP14,
  inout               IO_GP15
);

  logic clk_sys, clk_48mhz, rst_sys_n;
  logic [31:0] cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;
  logic cio_spi_device_sck_p2d, cio_spi_device_csb_p2d, cio_spi_device_mosi_p2d,
        cio_spi_device_miso_d2p, cio_spi_device_miso_en_d2p;
  logic cio_jtag_tck_p2d, cio_jtag_tms_p2d, cio_jtag_tdi_p2d, cio_jtag_tdo_d2p;
  logic cio_jtag_trst_n_p2d, cio_jtag_srst_n_p2d;
  logic cio_usbdev_sense_p2d;
  logic cio_usbdev_se0_d2p, cio_usbdev_se0_en_d2p;
  logic cio_usbdev_pullup_d2p, cio_usbdev_pullup_en_d2p;
  logic cio_usbdev_tx_mode_se_d2p, cio_usbdev_tx_mode_se_en_d2p;
  logic cio_usbdev_supsend_d2p, cio_usbdev_supsend_en_d2p;
  logic cio_usbdev_d_p2d, cio_usbdev_d_d2p, cio_usbdev_d_en_d2p;
  logic cio_usbdev_dp_p2d, cio_usbdev_dp_d2p, cio_usbdev_dp_en_d2p;
  logic cio_usbdev_dn_p2d, cio_usbdev_dn_d2p, cio_usbdev_dn_en_d2p;

  // TODO: instantiate padring and route these signals through that module
  logic [13:0] dio_in;
  logic [13:0] dio_out;
  logic [13:0] dio_oe;

  assign dio_in = {cio_spi_device_sck_p2d,
                   cio_spi_device_csb_p2d,
                   cio_spi_device_mosi_p2d,
                   1'b0,
                   cio_uart_rx_p2d,
                   1'b0,
                   cio_usbdev_sense_p2d,
                   1'b0,
                   1'b0,
                   1'b0,
                   1'b0,
                   cio_usbdev_d_p2d,
                   cio_usbdev_dp_p2d,
                   cio_usbdev_dn_p2d};

  assign cio_usbdev_dn_d2p = dio_out[0];
  assign cio_usbdev_dp_d2p = dio_out[1];
  assign cio_usbdev_d_d2p  = dio_out[2];
  assign cio_usbdev_suspend_d2p = dio_out[3];
  assign cio_usbdev_tx_mode_se_d2p = dio_out[4];
  assign cio_usbdev_pullup_d2p = dio_out[5];
  assign cio_usbdev_se0_d2p = dio_out[6];
  assign cio_uart_tx_d2p = dio_out[8];
  assign cio_spi_device_miso_d2p = dio_out[10];

  assign cio_usbdev_dn_en_d2p = dio_oe[0];
  assign cio_usbdev_dp_en_d2p = dio_oe[1];
  assign cio_usbdev_d_en_d2p  = dio_oe[2];
  assign cio_usbdev_suspend_en_d2p = dio_oe[3];
  assign cio_usbdev_tx_mode_se_en_d2p = dio_oe[4];
  assign cio_usbdev_pullup_en_d2p = dio_oe[5];
  assign cio_usbdev_se0_en_d2p = dio_oe[6];
  assign cio_uart_tx_en_d2p = dio_oe[8];
  assign cio_spi_device_miso_en_d2p = dio_oe[10];

  // Top-level design
  top_earlgrey #(
    .IbexPipeLine(1)
  ) top_earlgrey (
    .clk_i                      (clk_sys),
    .rst_ni                     (rst_sys_n),
    .clk_fixed_i                (clk_sys),
    .clk_usb_48mhz_i            (clk_48mhz),

    .jtag_tck_i                 (cio_jtag_tck_p2d),
    .jtag_tms_i                 (cio_jtag_tms_p2d),
    .jtag_trst_ni               (cio_jtag_trst_n_p2d),
    .jtag_td_i                  (cio_jtag_tdi_p2d),
    .jtag_td_o                  (cio_jtag_tdo_d2p),

    // Multiplexed I/O
    .mio_in_i                   (cio_gpio_p2d),
    .mio_out_o                  (cio_gpio_d2p),
    .mio_oe_o                   (cio_gpio_en_d2p),

    // Dedicated I/O
    .dio_in_i                   (dio_in),
    .dio_out_o                  (dio_out),
    .dio_oe_o                   (dio_oe),

    .scanmode_i                 (1'b0) // 1 for Scan
  );

  clkgen_xil7series clkgen (
    .IO_CLK(IO_CLK),
    .IO_RST_N(IO_RST_N & cio_jtag_srst_n_p2d),
    .clk_sys(clk_sys),
    .clk_48MHz(clk_48mhz),
    .rst_sys_n(rst_sys_n)
  );

  // pad control
  padctl padctl (
    // UART
    .cio_uart_rx_p2d,
    .cio_uart_tx_d2p,
    .cio_uart_tx_en_d2p,
    // USB
    .cio_usbdev_sense_p2d(cio_usbdev_sense_p2d),
    .cio_usbdev_se0_d2p(cio_usbdev_se0_d2p),
    .cio_usbdev_se0_en_d2p(cio_usbdev_se0_en_d2p),
    .cio_usbdev_pullup_d2p(cio_usbdev_pullup_d2p),
    .cio_usbdev_pullup_en_d2p(cio_usbdev_pullup_en_d2p),
    .cio_usbdev_tx_mode_se_d2p(cio_usbdev_tx_mode_se_d2p),
    .cio_usbdev_tx_mode_se_en_d2p(cio_usbdev_tx_mode_se_en_d2p),
    .cio_usbdev_suspend_d2p(cio_usbdev_suspend_d2p),
    .cio_usbdev_suspend_en_d2p(cio_usbdev_suspend_en_d2p),
    .cio_usbdev_d_p2d(cio_usbdev_d_p2d),
    .cio_usbdev_d_d2p(cio_usbdev_d_d2p),
    .cio_usbdev_d_en_d2p(cio_usbdev_d_en_d2p),
    .cio_usbdev_dp_p2d(cio_usbdev_dp_p2d),
    .cio_usbdev_dp_d2p(cio_usbdev_dp_d2p),
    .cio_usbdev_dp_en_d2p(cio_usbdev_dp_en_d2p),
    .cio_usbdev_dn_p2d(cio_usbdev_dn_p2d),
    .cio_usbdev_dn_d2p(cio_usbdev_dn_d2p),
    .cio_usbdev_dn_en_d2p(cio_usbdev_dn_en_d2p),
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
    .IO_DPS6,
    .IO_DPS7
  );

endmodule
