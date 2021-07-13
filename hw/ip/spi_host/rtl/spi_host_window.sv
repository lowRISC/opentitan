// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Module to manage TX FIFO window for Serial Peripheral Interface (SPI) host IP.
//

module spi_host_window (
  input  clk_i,
  input  rst_ni,
  input  tlul_pkg::tl_h2d_t win_i,
  output tlul_pkg::tl_d2h_t win_o,
  output logic [31:0]       tx_data_o,
  output logic [3:0]        tx_be_o,
  output logic              tx_valid_o,
  input        [31:0]       rx_data_i,
  output                    rx_ready_o
);

  localparam int AW=spi_host_reg_pkg::BlockAw;
  localparam int DW=32;

  logic [AW-1:0] addr;

  // Only support reads/writes to the data fifo window
  logic win_error;
  assign win_error = (tx_valid_o || rx_ready_o) &&
                     (addr != spi_host_reg_pkg::SPI_HOST_DATA_OFFSET);

  tlul_adapter_reg #(
    .RegAw(AW),
    .RegDw(DW)
  ) u_adapter (
    .clk_i,
    .rst_ni,
    .tl_i      (win_i),
    .tl_o      (win_o),
    .we_o      (tx_valid_o),
    .re_o      (rx_ready_o),
    .addr_o    (addr),
    .wdata_o   (tx_data_o),
    .be_o      (tx_be_o),
    .busy_i    ('0),
    .rdata_i   (rx_data_i),
    .error_i   (win_error)
  );

endmodule : spi_host_window
