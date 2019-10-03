// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey #(
  parameter bit IbexPipeLine = 0
) (
);
  // uart
  logic uart_rx_p2d;
  logic uart_tx_d2p;
  logic uart_tx_en_d2p;
  // gpio
  logic [31:0] gpio_gpio_p2d;
  logic [31:0] gpio_gpio_d2p;
  logic [31:0] gpio_gpio_en_d2p;
  // spi_device
  logic spi_device_sck_p2d;
  logic spi_device_csb_p2d;
  logic spi_device_mosi_p2d;
  logic spi_device_miso_d2p;
  logic spi_device_miso_en_d2p;
  // flash_ctrl
  // rv_timer
  // hmac
  // rv_plic

  input               scanmode_i  // 1 for Scan

  // Top instantiation
  top_earlgrey_core #(
    .IbexPipeLine (IbexPipeLine)
  ) u_core (
    .clk_i          (           ),
    .rst_ni         (           ),

    // JTAG
    .jtag_tck_i     (           ),
    .jtag_tms_i     (           ),
    .jtag_trst_ni   (           ),
    .jtag_td_i      (           ),
    .jtag_td_o      (           ),

    // Module CIO
    // uart
    .cio_uart_rx_p2d_i (uart_rx_p2d),
    .cio_uart_tx_d2p_o    (uart_tx_d2p),
    .cio_uart_tx_en_d2p_o (uart_tx_en_d2p),
    // gpio
    .cio_gpio_gpio_p2d_i (gpio_gpio_p2d),
    .cio_gpio_gpio_d2p_o    (gpio_gpio_d2p),
    .cio_gpio_gpio_en_d2p_o (gpio_gpio_en_d2p),
    // spi_device
    .cio_spi_device_sck_p2d_i (spi_device_sck_p2d),
    .cio_spi_device_csb_p2d_i (spi_device_csb_p2d),
    .cio_spi_device_mosi_p2d_i (spi_device_mosi_p2d),
    .cio_spi_device_miso_d2p_o    (spi_device_miso_d2p),
    .cio_spi_device_miso_en_d2p_o (spi_device_miso_en_d2p),
    // flash_ctrl
    // rv_timer
    // hmac
    // rv_plic

    .scanmode_i()
  );

endmodule

