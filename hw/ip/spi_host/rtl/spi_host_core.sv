// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Core Implemenation module for Serial Peripheral Interface (SPI) Host IP.
//

module spi_host_core #(
  parameter  int NumCS     = 1
) (
  input                             clk_i,
  input                             rst_ni,

  input spi_host_cmd_pkg::command_t command_i,
  input                             command_valid_i,
  output                            command_ready_o,
  input                             en_i,

  input        [31:0]               tx_data_i,
  input        [3:0]                tx_be_i,
  input                             tx_valid_i,
  output logic                      tx_ready_o,

  output logic [31:0]               rx_data_o,
  output logic                      rx_valid_o,
  input                             rx_ready_i,

  input                             sw_rst_i,

  // SPI Interface
  output logic                      sck_o,
  output logic [NumCS-1:0]          csb_o,
  output logic [3:0]                sd_o,
  output logic [3:0]                sd_en_o,
  input [3:0]                       sd_i,

  // Status bits
  output logic                      rx_stall_o,
  output logic                      tx_stall_o,
  output logic                      active_o
);

  logic       rx_valid_sr;
  logic       rx_ready_sr;
  logic       rx_last_sr;
  logic [7:0] rx_data_sr;
  logic       tx_valid_sr;
  logic       tx_ready_sr;
  logic       tx_flush_sr;
  logic [7:0] tx_data_sr;

  logic       wr_en;
  logic       rd_en;
  logic       wr_ready;
  logic       rd_ready;

  logic       sample_en;
  logic       shift_en;
  logic [1:0] speed;
  logic       full_cyc;
  logic       last_read;
  logic       last_write;

  spi_host_byte_merge u_merge (
    .clk_i,
    .rst_ni,
    .byte_i       (rx_data_sr),
    .byte_last_i  (rx_last_sr),
    .byte_valid_i (rx_valid_sr),
    .byte_ready_o (rx_ready_sr),
    .word_o       (rx_data_o),
    .word_valid_o (rx_valid_o),
    .word_ready_i (rx_ready_i),
    .sw_rst_i
  );

  spi_host_byte_select u_select (
    .clk_i,
    .rst_ni,
    .word_i       (tx_data_i),
    .word_be_i    (tx_be_i),
    .word_valid_i (tx_valid_i),
    .word_ready_o (tx_ready_o),
    .byte_o       (tx_data_sr),
    .byte_valid_o (tx_valid_sr),
    .byte_ready_i (tx_ready_sr),
    .flush_i      (tx_flush_sr),
    .sw_rst_i
  );

  spi_host_shift_register u_shift_reg (
    .clk_i,
    .rst_ni,
    .wr_en_i      (wr_en),
    .wr_ready_o   (wr_ready),
    .rd_en_i      (rd_en),
    .rd_ready_o   (rd_ready),
    .speed_i      (speed),
    .shift_en_i   (shift_en),
    .sample_en_i  (sample_en),
    .last_read_i  (last_read),
    .last_write_i (last_write),
    .full_cyc_i   (full_cyc),
    .tx_data_i    (tx_data_sr),
    .tx_valid_i   (tx_valid_sr),
    .tx_ready_o   (tx_ready_sr),
    .tx_flush_o   (tx_flush_sr),
    .rx_data_o    (rx_data_sr),
    .rx_valid_o   (rx_valid_sr),
    .rx_ready_i   (rx_ready_sr),
    .rx_last_o    (rx_last_sr),
    .sw_rst_i,
    .sd_o         (sd_o),
    .sd_i         (sd_i)
  );

  spi_host_fsm #(
    .NumCS(NumCS)
  ) u_fsm (
    .clk_i,
    .rst_ni,
    .en_i,
    .command_i,
    .command_valid_i,
    .command_ready_o,
    .sck_o,
    .csb_o,
    .sd_en_o,
    .last_read_o      (last_read),
    .last_write_o     (last_write),
    .wr_en_o          (wr_en),
    .sr_wr_ready_i    (wr_ready),
    .rd_en_o          (rd_en),
    .sr_rd_ready_i    (rd_ready),
    .sample_en_o      (sample_en),
    .shift_en_o       (shift_en),
    .speed_o          (speed),
    .full_cyc_o       (full_cyc),
    .sw_rst_i,
    .rx_stall_o,
    .tx_stall_o,
    .active_o
  );

endmodule : spi_host_core
