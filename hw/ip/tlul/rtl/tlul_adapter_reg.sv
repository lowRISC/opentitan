// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Tile-Link UL adapter for Register interface
 */

module tlul_adapter_reg import tlul_pkg::*; #(
  parameter  int RegAw = 8,
  parameter  int RegDw = 32, // Shall be matched with TL_DW
  localparam int RegBw = RegDw/8
) (
  input clk_i,
  input rst_ni,

  // TL-UL interface
  input  tl_h2d_t tl_i,
  output tl_d2h_t tl_o,

  // Register interface
  output logic             re_o,
  output logic             we_o,
  output logic [RegAw-1:0] addr_o,
  output logic [RegDw-1:0] wdata_o,
  output logic [RegBw-1:0] be_o,
  input        [RegDw-1:0] rdata_i,
  input                    error_i
);

  localparam int IW  = $bits(tl_i.a_source);
  localparam int SZW = $bits(tl_i.a_size);

  logic outstanding;    // Indicates current request is pending
  logic a_ack, d_ack;

  logic [RegDw-1:0] rdata;
  logic             error;

  logic [IW-1:0]  reqid;
  logic [SZW-1:0] reqsz;
  tl_d_op_e       rspop;

  assign a_ack   = tl_i.a_valid & tl_o.a_ready;
  assign d_ack   = tl_o.d_valid & tl_i.d_ready;
  // Request signal
  assign we_o    = a_ack & ((tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData));
  assign re_o    = a_ack & (tl_i.a_opcode == Get);
  assign addr_o  = tl_i.a_address[RegAw-1:0];
  assign wdata_o = tl_i.a_data;
  assign be_o    = tl_i.a_mask;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)    outstanding <= 1'b0;
    else if (a_ack) outstanding <= 1'b1;
    else if (d_ack) outstanding <= 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reqid <= '0;
      reqsz <= '0;
      rspop <= AccessAck;
    end else if (a_ack) begin
      reqid <= tl_i.a_source;
      reqsz <= tl_i.a_size;
      rspop <= (re_o) ? AccessAckData : AccessAck ;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata  <= '0;
      error <= 1'b0;
    end else if (a_ack) begin
      rdata <= rdata_i;
      error <= error_i | (tl_i.a_user.parity_en == 1'b1);
    end
  end

  assign tl_o = '{
    a_ready:  ~outstanding,
    d_valid:  outstanding,
    d_opcode: rspop,
    d_param:  '0,
    d_size:   reqsz,
    d_source: reqid,
    d_sink:   '0,
    d_data:   rdata,
    d_user:  '0,
    d_error: error
  };


  `ASSERT_INIT(MatchedWidthAssert, RegDw == top_pkg::TL_DW)

endmodule
