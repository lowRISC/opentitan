// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_artys7 (
  // Clock and Reset
  input               IO_CLK,
  input               IO_RST_N,
  // JTAG interface -- not hooked up at the moment
  //input               IO_JTCK,
  //input               IO_JTMS,
  //input               IO_JTDI,
  //input               IO_JTRST_N,
  //output              IO_JTDO,
  // UART interface
  input               IO_URX,
  output              IO_UTX,
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

  logic clk_sys, rst_sys_n;
  logic [31:0]  cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;

  // Unlike Nexys Video there is no separate JTAG controller, tie off for now
  logic IO_JTCK = 0;
  logic IO_JTMS = 0;
  logic IO_JTDI = 0;
  logic IO_JTRST_N = IO_RST_N;
  logic IO_JTDO;


  // Top-level design
  top_earlgrey top_earlgrey (
    .clk_i                  (clk_sys),
    .rst_ni                 (rst_sys_n),

    .jtag_tck_i             (IO_JTCK),
    .jtag_tms_i             (IO_JTMS),
    .jtag_trst_ni           (IO_JTRST_N),
    .jtag_td_i              (IO_JTDI),
    .jtag_td_o              (IO_JTDO),

    .dio_uart_rx_i          (cio_uart_rx_p2d),
    .dio_uart_tx_o          (cio_uart_tx_d2p),
    .dio_uart_tx_en_o       (cio_uart_tx_en_d2p),

    .mio_in_i               (cio_gpio_p2d),
    .mio_out_o              (cio_gpio_d2p),
    .mio_oe_o               (cio_gpio_en_d2p)
  );

  // Clock and reset
  clkgen_xil7series clkgen (
    .IO_CLK(IO_CLK),
    .IO_RST_N(IO_RST_N),
    .clk_sys(clk_sys),
    .rst_sys_n(rst_sys_n)
  );

  // pad control
  padctl padctl (
    // UART
    .cio_uart_rx_p2d,
    .cio_uart_tx_d2p,
    .cio_uart_tx_en_d2p,
    // GPIO
    .cio_gpio_p2d,
    .cio_gpio_d2p,
    .cio_gpio_en_d2p,
    // pads
    .IO_URX,
    .IO_UTX,
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
    .IO_GP15
  );

endmodule
