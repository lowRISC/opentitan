// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// TL-UL error responder module, used by tlul_socket_1n to help response
// to requests to no correct address space. Responses are always one cycle
// after request with no stalling unless response is stuck on the way out.

module tlul_err_resp (
  input                     clk_i,
  input                     rst_ni,
  input  tlul_pkg::tl_h2d_t tl_h_i,
  output tlul_pkg::tl_d2h_t tl_h_o
);
  import tlul_pkg::*;

  tl_a_op_e                          err_opcode;
  logic [$bits(tl_h_i.a_source)-1:0] err_source;
  logic [$bits(tl_h_i.a_size)-1:0]   err_size;
  logic                              err_req_pending, err_rsp_pending;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_req_pending <= 1'b0;
      err_source      <= {top_pkg::TL_AIW{1'b0}};
      err_opcode      <= Get;
      err_size        <= '0;
    end else if (tl_h_i.a_valid && tl_h_o.a_ready) begin
      err_req_pending <= 1'b1;
      err_source      <= tl_h_i.a_source;
      err_opcode      <= tl_h_i.a_opcode;
      err_size        <= tl_h_i.a_size;
    end else if (!err_rsp_pending) begin
      err_req_pending <= 1'b0;
    end
  end

  assign tl_h_o.a_ready  = ~err_rsp_pending & ~(err_req_pending & ~tl_h_i.d_ready);
  assign tl_h_o.d_valid  = err_req_pending | err_rsp_pending;
  assign tl_h_o.d_data   = '1; // Return all F
  assign tl_h_o.d_source = err_source;
  assign tl_h_o.d_sink   = '0;
  assign tl_h_o.d_param  = '0;
  assign tl_h_o.d_size   = err_size;
  assign tl_h_o.d_opcode = (err_opcode == Get) ? AccessAckData : AccessAck;
  assign tl_h_o.d_user   = '0;
  assign tl_h_o.d_error  = 1'b1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_rsp_pending <= 1'b0;
    end else if ((err_req_pending || err_rsp_pending) && !tl_h_i.d_ready) begin
      err_rsp_pending <= 1'b1;
    end else begin
      err_rsp_pending <= 1'b0;
    end
  end

  // Waive unused bits of tl_h_i
  logic unused_tl_h;
  assign unused_tl_h = &{1'b0,
                         tl_h_i.a_param, tl_h_i.a_address, tl_h_i.a_mask,
                         tl_h_i.a_data, tl_h_i.a_user, tl_h_i.d_ready};

endmodule
