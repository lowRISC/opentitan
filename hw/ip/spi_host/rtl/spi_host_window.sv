// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Module to manage TX FIFO window for Serial Peripheral Interface (SPI) host IP.
//

module spi_host_window (
  input  clk_i,
  input  rst_ni,
  input  tlul_pkg::tl_h2d_t rx_win_i,
  output tlul_pkg::tl_d2h_t rx_win_o,
  input  tlul_pkg::tl_h2d_t tx_win_i,
  output tlul_pkg::tl_d2h_t tx_win_o,
  output logic [31:0]       tx_data_o,
  output logic [3:0]        tx_be_o,
  output logic              tx_valid_o,
  input        [31:0]       rx_data_i,
  output logic              rx_ready_o
);

  localparam int AW = spi_host_reg_pkg::BlockAw;
  localparam int DW = 32;

  logic rx_we, tx_re;

  // Only support reads from the data RX fifo window
  logic  rx_access_error;
  assign rx_access_error = rx_we;

  tlul_adapter_reg #(
    .RegAw (AW),
    .RegDw (DW)
  ) u_adapter_rx (
    .clk_i,
    .rst_ni,
    .tl_i    (rx_win_i),
    .tl_o    (rx_win_o),
    .we_o    (rx_we),
    .re_o    (rx_ready_o),
    .addr_o  (),
    .wdata_o (),
    .be_o    (),
    .rdata_i (rx_data_i),
    .error_i (rx_access_error),
    .busy_i  ('0)
  );

  // Only support writes to the data TX fifo window
  logic  tx_access_error;
  assign tx_access_error = tx_re;

  tlul_adapter_reg #(
    .RegAw (AW),
    .RegDw (DW)
  ) u_adapter_tx (
    .clk_i,
    .rst_ni,
    .tl_i    (tx_win_i),
    .tl_o    (tx_win_o),
    .we_o    (tx_valid_o),
    .re_o    (tx_re),
    .addr_o  (),
    .wdata_o (tx_data_o),
    .be_o    (tx_be_o),
    .rdata_i ({DW{1'b0}}),
    .error_i (tx_access_error),
    .busy_i  ('0)
  );

endmodule : spi_host_window
