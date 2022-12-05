// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Read Buffers Dependency
//
// This module handles the dependency between response order FIFO
// and the buffers.
// Basically, it ensures that if an item queued up in the response
// FIFO is waiting for a specific buffer, that buffer is not de-allocated
// to serve a new request.
//

module flash_phy_rd_buf_dep import flash_phy_pkg::*;(
  input clk_i,
  input rst_ni,
  input en_i,
  input fifo_wr_i,
  input fifo_rd_i,
  input [NumBuf-1:0] wr_buf_i,
  input [NumBuf-1:0] rd_buf_i,
  output logic [NumBuf-1:0] dependency_o,
  output logic all_dependency_o
);

  // The following logic determines the dependency between entries in the read buffer
  // with items currently queued up for response.
  localparam int NumBufWidth = $clog2(NumBuf);

   // also need to add an assertion to check for overflows
  localparam int BufDepCntWidth = $clog2(RspOrderDepth + 1);
  logic [NumBuf-1:0][BufDepCntWidth-1:0] buf_dependency_cnt;

  // The logic below can be more simplified in an always_comb loop,
  // but the `i` assignment causes some lint tools to be mildly unhappy.
  // This separarate creation seems to be more tool friendly.
  logic [NumBuf-1:0][NumBufWidth-1:0] buf_mux_cnt;
  for(genvar i = 0; i < NumBuf; i++) begin : gen_cnt_assign
     assign buf_mux_cnt[i] = i;
  end

  // the dep buf select needs to be different between increment and decrement
  // When incrementing, we are looking at the wdata of the rsp_order_fifo
  // When decrementing, we are looking at the rdata of the rsp_order_fifo
  logic [NumBufWidth-1:0] incr_buf_sel;
  logic [NumBufWidth-1:0] decr_buf_sel;
  always_comb begin
    incr_buf_sel = '0;
    decr_buf_sel = '0;
    for (int unsigned i = 0; i < NumBuf; i++) begin
      if (wr_buf_i[i]) begin
        incr_buf_sel = buf_mux_cnt[i];
      end
      if (rd_buf_i[i]) begin
        decr_buf_sel = buf_mux_cnt[i];
      end
    end
  end // always_comb

  logic [BufDepCntWidth-1:0] curr_incr_cnt, curr_decr_cnt;
  assign curr_incr_cnt = buf_dependency_cnt[incr_buf_sel];
  assign curr_decr_cnt = buf_dependency_cnt[decr_buf_sel];

  logic cnt_incr, cnt_decr;
  assign cnt_incr = en_i & fifo_wr_i & (curr_incr_cnt < RspOrderDepth);
  assign cnt_decr = en_i & fifo_rd_i & (curr_decr_cnt > '0);

  //assign cnt_decr = fifo_rd_i & (rsp_fifo_vld & data_valid_o) & (curr_decr_cnt > '0);

  logic fin_cnt_incr, fin_cnt_decr;
  assign fin_cnt_incr = (incr_buf_sel == decr_buf_sel) ? cnt_incr && !cnt_decr : cnt_incr;
  assign fin_cnt_decr = (incr_buf_sel == decr_buf_sel) ? !cnt_incr && cnt_decr : cnt_decr;

  // This tells us which buffer currently has a dependency to an item in the rsp_order_fifo
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      buf_dependency_cnt <= '0;
    end else begin
       if (fin_cnt_incr) begin
          buf_dependency_cnt[incr_buf_sel] <= curr_incr_cnt + 1'b1;
       end
       if (fin_cnt_decr) begin
          buf_dependency_cnt[decr_buf_sel] <= curr_decr_cnt - 1'b1;
       end
    end
  end

  // per buffer dependency determination
  always_comb begin
    dependency_o = '0;
    for (int i = 0; i < NumBuf; i++) begin
      dependency_o[i] = |buf_dependency_cnt[i];
    end
  end

  // all buffer entries currently have a dependency
  assign all_dependency_o = &dependency_o;


  // If there are more buffers than there are number of response fifo entries, we an never have
  // a fully dependent condition
  `ASSERT(BufferDepRsp_A, NumBuf > RspOrderDepth |-> ~all_dependency_o)

  // We should never attempt to increment when at max value
  `ASSERT(BufferIncrOverFlow_A, en_i & fifo_wr_i |-> curr_incr_cnt < RspOrderDepth)

  // We should never attempt to decrement when at min value
  `ASSERT(BufferDecrUnderRun_A, en_i & fifo_rd_i |-> (curr_decr_cnt > '0))

  // The total number of dependent buffers cannot never exceed the size of response queue
  `ifdef INC_ASSERT
  //VCS coverage off
  // pragma coverage off
  logic [31:0] assert_cnt;
  always_comb begin
    assert_cnt = '0;
    for (int unsigned i = 0; i < NumBuf; i++) begin
      assert_cnt = assert_cnt + dependency_o[i];
    end
  end
  //VCS coverage on
  // pragma coverage on

  `ASSERT(DepBufferRspOrder_A, fifo_wr_i |=> assert_cnt <= RspOrderDepth)
  `endif


endmodule // flash_phy_rd_buf_dep
