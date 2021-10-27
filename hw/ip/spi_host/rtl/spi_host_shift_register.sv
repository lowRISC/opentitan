// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Shift Register for Serial Peripheral Interface (SPI) Host IP.
//

module spi_host_shift_register (
  input              clk_i,
  input              rst_ni,
  input              wr_en_i,
  output logic       wr_ready_o,
  input              rd_en_i,
  output logic       rd_ready_o,

  input        [1:0] speed_i,
  input              shift_en_i,
  input              sample_en_i,
  input              full_cyc_i,
  input              last_read_i,
  input              last_write_i,

  input        [7:0] tx_data_i,
  input              tx_valid_i,
  output             tx_ready_o,
  output             tx_flush_o,

  output logic [7:0] rx_data_o,
  output logic       rx_valid_o,
  input              rx_ready_i,
  output logic       rx_last_o,

  input        [3:0] sd_i,
  output logic [3:0] sd_o,

  input              sw_rst_i
);
  import spi_host_cmd_pkg::*;

  logic        [7:0] sr_q;
  logic        [7:0] sr_d;
  logic        [3:0] sd_i_q, sd_i_d;
  logic        [3:0] next_bits;
  logic        [7:0] sr_shifted;

  // 9-bit buffer to hold shift register data
  // and the last_read bit to indicate whether
  // it is the last in a series.
  logic        [8:0] rx_buf_q;
  logic        [8:0] rx_buf_d;
  logic              rx_buf_valid_q;
  logic              rx_buf_valid_d;

  `ASSERT(SpeedValid, speed_i != RsvdSpd, clk_i, rst_ni)

  assign next_bits  = full_cyc_i ? sd_i : sd_i_q;
  assign sr_shifted = (speed_i == Standard) ? {sr_q[6:0], next_bits[1]} :
                      (speed_i == Dual)     ? {sr_q[5:0], next_bits[1:0]} :
                      (speed_i == Quad)     ? {sr_q[3:0], next_bits[3:0]} :
                      8'h00;

  assign sd_o       = (speed_i == Standard) ? {3'b000, sr_q[7]}   :
                      (speed_i == Dual)     ? {2'b00,  sr_q[7:6]} :
                      (speed_i == Quad)     ? {sr_q[7:4]} :
                      4'h0;

  // Buffer the rx_data outputs to simplify three-way flow control
  // between fsm, shift reg and byte_merge.
  assign rd_ready_o             = ~rx_buf_valid_q | (rx_valid_o & rx_ready_i);
  assign rx_valid_o             = rx_buf_valid_q;

  assign rx_buf_d               = sw_rst_i                ? 9'h0 :
                                  (rd_en_i && rd_ready_o) ? {last_read_i, sr_shifted} :
                                  rx_buf_q;

  assign rx_buf_valid_d         = sw_rst_i                  ? 1'b0 :
                                  (rd_en_i && rd_ready_o)   ? 1'b1 :
                                  (rx_valid_o & rx_ready_i) ? 1'b0 :
                                  rx_buf_valid_q;

  assign sd_i_d                 = sw_rst_i    ? 4'b0 :
                                  sample_en_i ? sd_i :
                                  sd_i_q;

  assign {rx_last_o, rx_data_o} = rx_buf_q;

  // tx_data cannot be buffered, because of the
  // need to transmit tx_flush as we fetch the
  // last-needed byte.
  assign wr_ready_o         = tx_valid_i;
  assign tx_ready_o         = wr_en_i;
  assign tx_flush_o         = last_write_i;

  assign sr_d = sw_rst_i               ? 8'h0 :
                (wr_en_i & wr_ready_o) ? tx_data_i :
                shift_en_i             ? sr_shifted :
                sr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sd_i_q <= 4'h0;
      sr_q <= 8'h0;
      rx_buf_valid_q <= 1'b0;
      rx_buf_q <= 9'h0;
    end else begin
      sd_i_q <= sd_i_d;
      sr_q <= sr_d;
      rx_buf_valid_q <= rx_buf_valid_d;
      rx_buf_q <= rx_buf_d;
    end
  end

endmodule : spi_host_shift_register
