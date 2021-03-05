// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Provides termination for a TL interface.
module tlul_sink import tlul_pkg::*; (
  input logic clk_i,
  input logic rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o
);
  logic a_ack, d_ack;
  logic rd_req, wr_req;
  logic pending;

  localparam int IDW = $bits(tl_i.a_source);
  localparam int SZW = $bits(tl_i.a_size);

  logic [IDW-1:0] d_source_q;
  logic [SZW-1:0] d_size_q;
  tl_d_op_e       d_opcode_q;
  logic           d_error_q;

  logic addr_align_err;     // Size and alignment
  logic wr_mask_err;        // Write mask always all 1s.
  logic malformed_meta_err; // User signal format error or unsupported
  logic tl_err;             // Common TL-UL error checker

  assign a_ack   = tl_i.a_valid & tl_o.a_ready;
  assign d_ack   = tl_o.d_valid & tl_i.d_ready;
  assign wr_req  = a_ack & ((tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData));
  assign rd_req  = a_ack & (tl_i.a_opcode == Get);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)    pending <= 1'b0;
    else if (a_ack) pending <= 1'b1;
    else if (d_ack) pending <= 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      d_source_q <= '0;
      d_size_q <= '0;
      d_opcode_q <= AccessAck;
      d_error_q <= 1'b0;
    end else if (a_ack) begin
      d_source_q <= tl_i.a_source;
      d_size_q <= tl_i.a_size;
      d_opcode_q <= rd_req ? AccessAckData : AccessAck;
      d_error_q <= (addr_align_err | wr_mask_err | malformed_meta_err | tl_err);
    end
  end

  ////////////////////
  // Error Handling //
  ////////////////////
  // Accept only word aligned address.
  assign addr_align_err = wr_req ? (|tl_i.a_address[1:0]) : 1'b0;

  // Write mask should be all 1s.
  assign wr_mask_err = wr_req ? ~(&tl_i.a_mask) : 1'b0;

  // Don't allow unsupported values.
  assign malformed_meta_err = tl_a_user_chk(tl_i.a_user);

  // tl_err : separate checker
  tlul_err u_err (
    .clk_i,
    .rst_ni,
    .tl_i,
    .err_o (tl_err)
  );

  //////////////////
  // Final Output //
  //////////////////
  tlul_pkg::tl_d2h_t tl_o_pre;
  assign tl_o_pre = '{
    a_ready:  ~pending,
    d_valid:  pending,
    d_opcode: d_opcode_q,
    d_param:  '0,
    d_size:   d_size_q,
    d_source: d_source_q,
    d_sink:   '0,
    d_data:   '0,
    d_user:   '0,
    d_error:  d_error_q
  };

  tlul_rsp_intg_gen u_gen (
    .tl_i(tl_o_pre),
    .tl_o
  );

endmodule
