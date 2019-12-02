// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_usb_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni
  );

  localparam MAX_USB=1;

  logic cio_jtag_tck, cio_jtag_tms, cio_jtag_tdi, cio_jtag_tdo;
  logic cio_jtag_trst_n, cio_jtag_srst_n;

  logic [31:0]  cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;
  logic dio_usb_dp_p2d[MAX_USB], dio_usb_dp_d2p[MAX_USB], dio_usb_dp_en_d2p[MAX_USB];
  logic dio_usb_dn_p2d[MAX_USB], dio_usb_dn_d2p[MAX_USB], dio_usb_dn_en_d2p[MAX_USB];
  logic dio_usb_sense_p2d[MAX_USB], dio_usb_pullup_d2p[MAX_USB], dio_usb_pullup_en_d2p[MAX_USB];

  logic cio_spi_device_sck_p2d, cio_spi_device_csb_p2d;
  logic cio_spi_device_mosi_p2d;
  logic cio_spi_device_miso_d2p, cio_spi_device_miso_en_d2p;

  logic IO_JTCK, IO_JTMS, IO_JTRST_N, IO_JTDI, IO_JTDO;

  // Top-level design
  top_earlgrey_usb #(
    .MAX_USB(1),
    .N_USB(1),
    .USB_UART(0),
    .USB_DEVICE(1)
  ) top_earlgrey_usb  (
    .clk_i                    (clk_i),
    .rst_ni                   (rst_ni),

    .jtag_tck_i               (IO_JTCK),
    .jtag_tms_i               (IO_JTMS),
    .jtag_trst_ni             (rst_ni),
    .jtag_td_i                (IO_JTDI),
    .jtag_td_o                (IO_JTDO),

    .dio_uart_rx_i            (cio_uart_rx_p2d),
    .dio_uart_tx_o            (cio_uart_tx_d2p),
    .dio_uart_tx_en_o         (cio_uart_tx_en_d2p),

    .clk_48mhz_i              (clk_i),
    .dio_usb_dp_i             (dio_usb_dp_p2d),
    .dio_usb_dp_o             (dio_usb_dp_d2p),
    .dio_usb_dp_en_o          (dio_usb_dp_en_d2p),
    .dio_usb_dn_i             (dio_usb_dn_p2d),
    .dio_usb_dn_o             (dio_usb_dn_d2p),
    .dio_usb_dn_en_o          (dio_usb_dn_en_d2p),
    .dio_usb_sense_i          (dio_usb_sense_p2d),
    .dio_usb_pullup_o         (dio_usb_pullup_d2p),
    .dio_usb_pullup_en_o      (dio_usb_pullup_en_d2p),

    .mio_in_i                 (cio_gpio_p2d),
    .mio_out_o                (cio_gpio_d2p),
    .mio_oe_o                 (cio_gpio_en_d2p),

    .dio_spi_device_sck_i     (cio_spi_device_sck_p2d),
    .dio_spi_device_csb_i     (cio_spi_device_csb_p2d),
    .dio_spi_device_mosi_i    (cio_spi_device_mosi_p2d),
    .dio_spi_device_miso_o    (cio_spi_device_miso_d2p),
    .dio_spi_device_miso_en_o (cio_spi_device_miso_en_d2p),

    .scanmode_i               (1'b0)
  );

  // GPIO DPI
  gpiodpi
    #(.N_GPIO(32))
    u_gpiodpi(
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .gpio_p2d(cio_gpio_p2d),
      .gpio_d2p(cio_gpio_d2p),
      .gpio_en_d2p(cio_gpio_en_d2p)
  );

  // UART DPI
  // The baud rate set to match FPGA implementation; the frequency is
  // "artificial".
  // Both baud rate and frequency must match the settings used in the on-chip
  // software.
  uartdpi #(
    .BAUD('d9_600),
    .FREQ('d500_000)
  ) u_uart (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .tx_o   (cio_uart_rx_p2d),
    .rx_i   (cio_uart_tx_d2p)
  );

  // USB DPI
  usbdpi udpi (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clk_48MHz_i    (clk_i),
    .dp_p2d         (dio_usb_dp_p2d[0]),
    .dp_d2p         (dio_usb_dp_d2p[0]),
    .dp_en_d2p      (dio_usb_dp_en_d2p[0]),
    .dn_p2d         (dio_usb_dn_p2d[0]),
    .dn_d2p         (dio_usb_dn_d2p[0]),
    .dn_en_d2p      (dio_usb_dn_en_d2p[0]),
    .sense_p2d      (dio_usb_sense_p2d[0]),
    .pullup_d2p     (dio_usb_pullup_d2p[0]),
    .pullup_en_d2p  (dio_usb_pullup_en_d2p[0])
  );

  // JTAG DPI for OpenOCD
  jtagdpi u_jtagdpi (
    .clk_i,
    .rst_ni,

    .jtag_tck    (cio_jtag_tck),
    .jtag_tms    (cio_jtag_tms),
    .jtag_tdi    (cio_jtag_tdi),
    .jtag_tdo    (cio_jtag_tdo),
    .jtag_trst_n (cio_jtag_trst_n),
    .jtag_srst_n (cio_jtag_srst_n)
  );

  // SPI DPI
  spidpi u_spi (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .spi_device_sck_o     (cio_spi_device_sck_p2d),
    .spi_device_csb_o     (cio_spi_device_csb_p2d),
    .spi_device_mosi_o    (cio_spi_device_mosi_p2d),
    .spi_device_miso_i    (cio_spi_device_miso_d2p),
    .spi_device_miso_en_i (cio_spi_device_miso_en_d2p)
  );

endmodule
