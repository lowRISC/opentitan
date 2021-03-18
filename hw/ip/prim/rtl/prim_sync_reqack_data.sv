// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// REQ/ACK synchronizer with associated data.
//
// This module synchronizes a REQ/ACK handshake with associated data across a clock domain
// crossing (CDC). Both domains will see a handshake with the duration of one clock cycle. By
// default, the data itself is not registered. The main purpose of feeding the data through this
// module to have an anchor point for waiving CDC violations. If the data is configured to flow
// from the destination (DST) to the source (SRC) domain, an additional register stage can be
// inserted for data buffering.
//
// Under the hood, this module uses a prim_sync_reqack primitive for synchronizing the
// REQ/ACK handshake. See prim_sync_reqack.sv for more details.

`include "prim_assert.sv"

module prim_sync_reqack_data #(
  parameter int unsigned Width       = 1,
  parameter bit          DataSrc2Dst = 1'b1, // Direction of data flow: 1'b1 = SRC to DST,
                                             //                         1'b0 = DST to SRC
  parameter bit          DataReg     = 1'b0, // Enable optional register stage for data,
                                             // only usable with DataSrc2Dst == 1'b0.
  parameter bit EnReqStabA = 1               // Used in submodule `prim_sync_reqack`.
) (
  input  clk_src_i,       // REQ side, SRC domain
  input  rst_src_ni,      // REQ side, SRC domain
  input  clk_dst_i,       // ACK side, DST domain
  input  rst_dst_ni,      // ACK side, DST domain

  input  logic src_req_i, // REQ side, SRC domain
  output logic src_ack_o, // REQ side, SRC domain
  output logic dst_req_o, // ACK side, DST domain
  input  logic dst_ack_i, // ACK side, DST domain

  input  logic [Width-1:0] data_i,
  output logic [Width-1:0] data_o
);

  ////////////////////////////////////
  // REQ/ACK synchronizer primitive //
  ////////////////////////////////////
  prim_sync_reqack #(
    .EnReqStabA(EnReqStabA)
  ) u_prim_sync_reqack (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,

    .src_req_i,
    .src_ack_o,
    .dst_req_o,
    .dst_ack_i
  );

  /////////////////////////
  // Data register stage //
  /////////////////////////
  // Optional - Only relevant if the data flows from DST to SRC. In this case, it must be ensured
  // that the data remains stable until the ACK becomes visible in the SRC domain.
  //
  // Note that for larger data widths, it is recommended to adjust the data sender to hold the data
  // stable until the next REQ in order to save the cost of this register stage.
  if (DataSrc2Dst == 1'b0 && DataReg == 1'b1) begin : gen_data_reg
    logic             data_we;
    logic [Width-1:0] data_d, data_q;

    // Sample the data when seing the REQ/ACK handshake in the DST domain.
    assign data_we = dst_req_o & dst_ack_i;
    assign data_d  = data_i;
    always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
      if (!rst_dst_ni) begin
        data_q <= '0;
      end else if (data_we) begin
        data_q <= data_d;
      end
    end
    assign data_o = data_q;

  end else begin : gen_no_data_reg
    // Just feed through the data.
    assign data_o = data_i;
  end

  ////////////////
  // Assertions //
  ////////////////
  if (DataSrc2Dst == 1'b1) begin : gen_assert_data_src2dst
    // SRC domain cannot change data while waiting for ACK.
    `ASSERT(SyncReqAckDataHoldSrc2Dst, !$stable(data_i) |->
        (!src_req_i || (src_req_i && src_ack_o)),
        clk_src_i, !rst_src_ni)

    // Register stage cannot be used.
    `ASSERT_INIT(SyncReqAckDataReg, DataSrc2Dst && !DataReg)

  end else if (DataSrc2Dst == 1'b0 && DataReg == 1'b0) begin : gen_assert_data_dst2src
    // DST domain shall not change data while waiting for SRC domain to latch it (together with
    // receiving ACK). It takes 2 SRC cycles for ACK to cross over from DST to SRC, and 1 SRC cycle
    // for the next REQ to cross over from SRC to DST. Assert that the data is stable during that
    // window, i.e. [-2,+1] SRC cycles around the SRC handshake.
    `ASSERT(SyncReqAckDataHoldDst2Src,
        src_req_i && src_ack_o |-> $past(data_o,2) == data_o && $stable(data_o) [*2],
        clk_src_i, !rst_src_ni)
  end

endmodule
