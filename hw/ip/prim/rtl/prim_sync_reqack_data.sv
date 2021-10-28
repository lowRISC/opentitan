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
  parameter bit          DataReg     = 1'b0  // Enable optional register stage for data,
                                             // only usable with DataSrc2Dst == 1'b0.
) (
  input  clk_src_i,       // REQ side, SRC domain
  input  rst_src_ni,      // REQ side, SRC domain
  input  clk_dst_i,       // ACK side, DST domain
  input  rst_dst_ni,      // ACK side, DST domain

  input  logic req_chk_i, // Used for gating assertions. Drive to 1 during normal operation.

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
  prim_sync_reqack u_prim_sync_reqack (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,

    .req_chk_i,

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
    // for the next REQ to cross over from SRC to DST.
    //
    // Denote the src clock where REQ & ACK as time zero. The data flowing through the CDC could be
    // corrupted if data_o was not stable over the previous 2 clock cycles (so we want to check time
    // points -2, -1 and 0). Moreover, the DST domain cannot know that it is allowed to change value
    // until at least one more SRC cycle (the time taken for REQ to cross back from SRC to DST).
    //
    // To make this assertion, we will sample at each of 4 time points (-2, -1, 0 and +1), asserting
    // that data_o is equal at each of these times. Note this won't detect glitches at intermediate
    // timepoints.
    //
    // The SVAs below are designed not to consume time, which means that they can be disabled with
    // an $assertoff(..) and won't linger to fail later. This wouldn't work properly if we used
    // something like |=> instead of the $past(...) function. That means that we have to trigger at
    // the "end" of the window. To make sure we don't miss a situation where the value changed at
    // time -1 (causing corruption), but reset was asserted between time 0 and 1, we split the
    // assertion into two pieces. The first (SyncReqAckDataHoldDst2SrcA) checks that data doesn't
    // change in a way that could cause data corruption. The second (SyncReqAckDataHoldDst2SrcB)
    // checks that the DST side doesn't do anything that it shouldn't know is safe.
    `ASSERT(SyncReqAckDataHoldDst2SrcA,
            src_req_i && src_ack_o |-> $past(data_o, 2) == data_o && $past(data_o) == data_o,
            clk_src_i, !rst_src_ni)
    `ASSERT(SyncReqAckDataHoldDst2SrcB,
            $past(src_req_i && src_ack_o) |-> $past(data_o) == data_o,
            clk_src_i, !rst_src_ni)
  end

endmodule
