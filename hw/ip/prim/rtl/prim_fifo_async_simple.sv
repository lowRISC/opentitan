// Copyright lowRISC contributors (OpenTitan project).
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

  // write side
  logic wr_en;
  logic src_req, src_ack;
  logic pending_d, pending_q, not_in_reset_q;
  logic [Width-1:0] data_wr_q;

  // read side
  logic             rvalid_q;
  logic             rvalid_d;
  logic             dst_req;
  logic             dst_ack;
  logic [Width-1:0] data_rd_q;

  //////////////////
  // Write domain //
  //////////////////

  ////////////////
  // FIFO logic //
  ////////////////
  // Convert ready/valid to req/ack
  assign wready_o = !pending_q && not_in_reset_q;
  assign wr_en = wvalid_i && wready_o;
  assign src_req = pending_q || wvalid_i;

  assign pending_d = (src_ack)  ? 1'b0 :
                     (wr_en)    ? 1'b1 : pending_q;

  always_ff @(posedge clk_wr_i or negedge rst_wr_ni) begin
    if (!rst_wr_ni) begin
      pending_q <= 1'b0;
      not_in_reset_q <= 1'b0;
    end else begin
      pending_q <= pending_d;
      not_in_reset_q <= 1'b1;
    end
  end

  // Data holding reg
  always_ff @(posedge clk_wr_i) begin
    if (wr_en) begin
      data_wr_q <= wdata_i;
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

  /////////////////
  // Read domain //
  /////////////////
  // This flop realigns the request signal to the data
  // and manages the ready/valid to ack/req protocol
  always_comb begin

    rvalid_d = rvalid_q;

    if (!rvalid_q) begin
      if (dst_req) begin
        rvalid_d = '1;
      end
    end else begin
      if (rready_i) begin
        rvalid_d = '0;
      end
    end

  end

  always_ff @(posedge clk_rd_i or negedge rst_rd_ni) begin
    if (!rst_rd_ni) begin
      rvalid_q <= '0;
    end else begin
      rvalid_q <= rvalid_d;
    end
  end

  // Output staging registers in the read domain to ensure data is synchronous
  // and enable correct back pressure in the pipe.
  // NOTE: data_rd_q must be read before it can be updated, i.e. rvalid_q is low,
  // otherwise data that has not yet been read would be overwritten.
  always_ff @(posedge clk_rd_i) begin
    if (dst_req && !rvalid_q) begin
      data_rd_q <= data_wr_q;
    end
  end

  assign rdata_o  = data_rd_q;

  // condition the dst_ack and pass the state to rvalid
  assign dst_ack = !rvalid_q ? dst_req : 1'b0;
  assign rvalid_o = rvalid_q;

endmodule
