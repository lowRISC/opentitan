// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`include "prim_assert.sv"

module prim_fifo_async_simple #(
  parameter int unsigned Width  = 16,
  parameter bit          EnRstChks = 1'b0, // Enable reset-related assertion checks, disabled by
                                           // default.
  parameter bit          EnRzHs = 1'b0     // By Default, the faster NRZ handshake protocol
                                           // (EnRzHs = 0) is used. Enable the RZ handshake protocol
                                           // if the FSMs need to be partial-reset-safe.
) (
  // write port
  input  logic              clk_wr_i,
  input  logic              rst_wr_ni,
  input  logic              wvalid_i,
  output logic              wready_o,
  input  logic [Width-1:0]  wdata_i,

  // read port
  input  logic              clk_rd_i,
  input  logic              rst_rd_ni,
  output logic              rvalid_o,
  input  logic              rready_i,
  output logic [Width-1:0]  rdata_o
);

  ////////////////
  // FIFO logic //
  ////////////////

  // Convert ready/valid to req/ack
  logic wr_en;
  logic src_req, src_ack;
  logic pending_d, pending_q, not_in_reset_q;
  assign wready_o = !pending_q && not_in_reset_q;
  assign wr_en = wvalid_i && wready_o;
  assign src_req = pending_q || wvalid_i;

  assign pending_d = (src_ack)  ? 1'b0 :
                     (wr_en)    ? 1'b1 : pending_q;

  logic dst_req, dst_ack;
  assign rvalid_o = dst_req;
  assign dst_ack = dst_req && rready_i;

  always_ff @(posedge clk_wr_i or negedge rst_wr_ni) begin
    if (!rst_wr_ni) begin
      pending_q <= 1'b0;
      not_in_reset_q <= 1'b0;
    end else begin
      pending_q <= pending_d;
      not_in_reset_q <= 1'b1;
    end
  end

  ////////////////////////////////////
  // REQ/ACK synchronizer primitive //
  ////////////////////////////////////

  prim_sync_reqack #(
    .EnRstChks(EnRstChks),
    .EnRzHs(EnRzHs)
  ) u_prim_sync_reqack (
    .clk_src_i(clk_wr_i),
    .rst_src_ni(rst_wr_ni),
    .clk_dst_i(clk_rd_i),
    .rst_dst_ni(rst_rd_ni),
    .req_chk_i(1'b0),
    .src_req_i(src_req),
    .src_ack_o(src_ack),
    .dst_req_o(dst_req),
    .dst_ack_i(dst_ack)
  );

  //////////////////////
  // Data holding reg //
  //////////////////////

  logic [Width-1:0] data_q;
  always_ff @(posedge clk_wr_i) begin
    if (wr_en) begin
      data_q <= wdata_i;
    end
  end
  assign rdata_o = data_q;

endmodule
