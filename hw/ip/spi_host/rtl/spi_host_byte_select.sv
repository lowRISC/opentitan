// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Byte-select module for dispensing words in SPI Host IP
//
module spi_host_byte_select (
  input               clk_i,
  input               rst_ni,
  input       [31:0]  word_i,
  input        [3:0]  word_be_i,
  input               word_valid_i,
  output logic        word_ready_o,
  output logic  [7:0] byte_o,
  output logic        byte_valid_o,
  input               byte_ready_i,
  input               flush_i,
  input               sw_rst_i
);

  logic       [35:0]  wdata_be;
  logic               do_drain;
  logic               byte_en;
  logic               byte_valid;
  logic               byte_ready;
  logic               clr;

  assign clr          = flush_i | sw_rst_i;
  assign byte_valid_o = byte_valid & byte_en;
  assign do_drain     = byte_valid & ~byte_en;
  assign byte_ready   = byte_ready_i | do_drain;

  for(genvar ii = 0; ii < 4; ii = ii + 1) begin : gen_map_data_be
    assign wdata_be[9*ii +: 9] = { word_be_i[ii], word_i[8*ii +: 8] };
  end : gen_map_data_be

  prim_packer_fifo #(
    .InW(36),
    .OutW(9)
  ) u_packer (
    .clk_i,
    .rst_ni,
    .clr_i     (clr),
    .wdata_i   (wdata_be),
    .wvalid_i  (word_valid_i),
    .wready_o  (word_ready_o),
    .rdata_o   ({byte_en, byte_o}),
    .rvalid_o  (byte_valid),
    .rready_i  (byte_ready),
    .depth_o   ()
  );

endmodule : spi_host_byte_select
