// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// tlul to wfifo interface
//
//

module flash_tlul_to_fifo #(
  parameter Dir = 0, //write0, read1
  parameter Size = 32
) (
  input                     clk_i,
  input                     rst_ni,
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  output                    fifo_wen_o,
  output [Size-1:0]         fifo_wdata_o,
  input                     fifo_full_i,
  output                    fifo_ren_o,
  input                     fifo_empty_i,
  input [Size-1:0]          fifo_rdata_i
);

  import tlul_pkg::*;
  import flash_ctrl_pkg::*;

  // This module just takes a tlul input interface and converts it to a FIFO wr side interface
  // Normally this can easily wired up, but this module will be used to to do some basic error
  // checking and response generation

  logic accepted;
  logic [top_pkg::TL_SZW-1:0] size;
  logic [top_pkg::TL_AIW-1:0] source;
  logic err;
  logic vld_op;
  logic req_stall;
  logic rsp_stall;

  if (Dir == WriteDir) begin : gen_valid_wr_ops
    // Only support write operations
    assign vld_op = tl_i.a_opcode == PutFullData | tl_i.a_opcode == PutPartialData;
    assign req_stall = fifo_full_i | rsp_stall;
    assign tl_o.d_opcode = AccessAck;
  end else begin : gen_valid_rd_ops
    // Only support read operations
    assign vld_op = tl_i.a_opcode == Get;
    assign req_stall = fifo_empty_i | rsp_stall;
    assign tl_o.d_opcode = AccessAckData;
  end

  // If a response is held of by host, stop accepting new requests
  assign rsp_stall = accepted & ~tl_i.d_ready;

  // assignments to fifo interface
  assign fifo_wen_o = tl_i.a_valid & ~req_stall;
  assign fifo_wdata_o = tl_i.a_data;
  assign fifo_ren_o = accepted;

  // Generate response on the following cycle of request acceptance
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      accepted <= 1'b0;
      size <= '0;
      source <= '0;
      err <= '0;
    end else if (fifo_wen_o) begin
      accepted <= 1'b1;
      size <= tl_i.a_size;
      source <= tl_i.a_source;
      err <= ~vld_op;
    end else if (accepted && tl_i.d_ready) begin
      accepted <= 1'b0;
      err <= 1'b0;
    end
  end

  // assignments to tlul interface
  assign tl_o.d_valid  = accepted;
  assign tl_o.d_param  = '0;
  assign tl_o.d_size   = size;
  assign tl_o.d_source = source;
  assign tl_o.d_sink   = 1'b0;
  assign tl_o.d_data   = fifo_rdata_i;
  assign tl_o.d_user   = '0;
  assign tl_o.d_error  = err;
  assign tl_o.a_ready  = ~req_stall;


  //unused nets
  logic [top_pkg::TL_AW-1:0] unused_addr;
  logic [top_pkg::TL_DBW-1:0] unused_mask;
  logic [2:0] unused_param;
  tl_a_user_t unused_user_bits;
  logic unused_full;
  logic unused_empty;

  assign unused_addr = tl_i.a_address;
  assign unused_mask = tl_i.a_mask;
  assign unused_param = tl_i.a_param;
  assign unused_user_bits = tl_i.a_user;

  if (Dir == WriteDir) begin : gen_wr_unused
    assign unused_empty = fifo_empty_i;
    assign unused_full = 1'b0;
  end else begin : gen_rd_unused
    assign unused_full = fifo_full_i;
    assign unused_empty = 1'b0;
  end



endmodule // flash_tlul_to_wfifo
