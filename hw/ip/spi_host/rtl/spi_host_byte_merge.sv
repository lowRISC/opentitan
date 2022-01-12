// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Byte-merge module for collecting words in SPI Host IP
//

module spi_host_byte_merge (
  input               clk_i,
  input               rst_ni,
  input        [7:0]  byte_i,
  input               byte_last_i,
  input               byte_valid_i,
  output logic        byte_ready_o,
  output logic [31:0] word_o,
  output logic        word_valid_o,
  input               word_ready_i,
  input               sw_rst_i
);

  logic               clr;
  logic               byte_valid;
  logic               byte_ready;
  logic               last_q;
  logic               last_d;
  logic               do_fill;
  logic               byte_incoming;

  // Don't clear data except on reset;
  assign clr = sw_rst_i;
  assign byte_incoming = byte_valid_i & byte_ready_o;

  assign last_d       = sw_rst_i                     ? 1'b0 :
                        byte_incoming && byte_last_i ? 1'b1 :
                        word_valid_o                 ? 1'b0 :
                        last_q;

  assign do_fill      = last_q & ~word_valid_o;
  assign byte_valid   = do_fill | byte_valid_i;
  assign byte_ready_o = byte_ready & ~do_fill;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_q <= 1'b0;
    end else begin
      last_q <= last_d;
    end
  end

  prim_packer_fifo #(
    .InW(8),
    .OutW(32)
  ) u_packer (
    .clk_i,
    .rst_ni,
    .clr_i    (clr),
    .wdata_i  (do_fill ? 8'h0 : byte_i),
    .wvalid_i (byte_valid),
    .wready_o (byte_ready),
    .rdata_o  (word_o),
    .rvalid_o (word_valid_o),
    .rready_i (word_ready_i),
    .depth_o  ()
  );

endmodule : spi_host_byte_merge
