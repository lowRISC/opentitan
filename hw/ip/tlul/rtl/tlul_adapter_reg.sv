// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL adapter for Register interface
 */

module tlul_adapter_reg import tlul_pkg::*; #(
  parameter  bit EnableDataIntgGen = 1'b0,
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
  logic             error, err_internal;

  logic addr_align_err;     // Size and alignment
  logic malformed_meta_err; // User signal format error or unsupported
  logic tl_err;             // Common TL-UL error checker

  logic [IW-1:0]  reqid;
  logic [SZW-1:0] reqsz;
  tl_d_op_e       rspop;

  logic rd_req, wr_req;

  assign a_ack   = tl_i.a_valid & tl_o.a_ready;
  assign d_ack   = tl_o.d_valid & tl_i.d_ready;
  // Request signal
  assign wr_req  = a_ack & ((tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData));
  assign rd_req  = a_ack & (tl_i.a_opcode == Get);

  assign we_o    = wr_req & ~err_internal;
  assign re_o    = rd_req & ~err_internal;
  assign wdata_o = tl_i.a_data;
  assign be_o    = tl_i.a_mask;

  if (RegAw <= 2) begin : gen_only_one_reg
    assign addr_o  = '0;
  end else begin : gen_more_regs
    assign addr_o  = {tl_i.a_address[RegAw-1:2], 2'b00}; // generate always word-align
  end

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
      // Return AccessAckData regardless of error
      rspop <= (rd_req) ? AccessAckData : AccessAck ;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata  <= '0;
      error <= 1'b0;
    end else if (a_ack) begin
      rdata <= (error_i || err_internal || wr_req) ? '1 : rdata_i;
      error <= error_i | err_internal;
    end
  end

  logic [DataIntgWidth-1:0] data_intg;
  if (EnableDataIntgGen) begin : gen_data_intg
    logic [DataMaxWidth-1:0] unused_data;

    prim_secded_64_57_enc u_data_gen (
      .in(DataMaxWidth'(rdata)),
      .out({data_intg, unused_data})
    );
  end else begin : gen_tieoff_data_intg
    assign data_intg = '0;
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
    d_user:   '{default: '0, data_intg: data_intg},
    d_error:  error
  };

  ////////////////////
  // Error Handling //
  ////////////////////
  assign err_internal = addr_align_err | malformed_meta_err | tl_err ;

  // Don't allow unsupported values.
  assign malformed_meta_err = tl_a_user_chk(tl_i.a_user);

  // addr_align_err
  //    Raised if addr isn't aligned with the size
  //    Read size error is checked in tlul_assert.sv
  //    Here is it added due to the limitation of register interface.
  always_comb begin
    if (wr_req) begin
      // Only word-align is accepted based on comportability spec
      addr_align_err = |tl_i.a_address[1:0];
    end else begin
      // No request
      addr_align_err = 1'b0;
    end
  end

  // tl_err : separate checker
  tlul_err u_err (
    .clk_i,
    .rst_ni,
    .tl_i,
    .err_o (tl_err)
  );

  `ASSERT_INIT(MatchedWidthAssert, RegDw == top_pkg::TL_DW)

endmodule
