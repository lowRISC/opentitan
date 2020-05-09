// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Read Module
//
// This module implements the flash phy read pipeline.
// The read pipeline consists of read buffers, the actual flash read stage, the
// descrambling stage, and finally the response.
//
// Note this module backpressures the front end, but cannot handle any back end
// back pressuring at the response stage.  It is thus assumed it will tell the
// upstream to stop issuing instructions, however once issued, the upstream will
// always accept the response.

module flash_phy_rd import flash_phy_pkg::*; (
  input clk_i,
  input rst_ni,

  // interface with arbitration unit
  input req_i,
  input prog_i,
  input pg_erase_i,
  input bk_erase_i,
  input [BankAddrW-1:0] addr_i,
  output logic rdy_o,
  output logic data_valid_o,
  output logic [BusWidth-1:0] data_o,
  output logic idle_o, // the entire read pipeline is idle

  // interface to actual flash primitive
  output logic req_o,
  input ack_i,
  input [DataWidth-1:0] data_i
  );

  /////////////////////////////////
  // Read buffers
  /////////////////////////////////

  // A buffer allocate is invoked when a new transaction arrives.
  // Alloc only happens if the new transaction does not match an existing entry.
  logic [NumBuf-1:0] alloc;

  // A buffer update is invoked after the completion of the de-scramble stage.
  // This updates the buffer that was allocated when a new transaction was initiated.
  logic [NumBuf-1:0] update;

  rd_buf_t read_buf [NumBuf];
  logic [NumBuf-1:0] buf_invalid;
  logic [NumBuf-1:0] buf_valid;
  logic [NumBuf-1:0] buf_wip;

  // The new transaction matches an already allocated buffer.
  // The buffer may be valid or work in progress.
  logic [NumBuf-1:0] buf_match;
  logic no_match;

  // There is a stateful operation aimed at valid buffer, that buffer must be flushed
  logic [NumBuf-1:0] data_hazard;

  // The next buffer allocated is determined in the following way:
  // If there is an invalid buffer, use that lowest one
  // If there are no invalid buffers, pick a valid buffer
  // Work in progress buffer is NEVER replaced.
  // There should only be one work in progress buffer at a time
  logic [NumBuf-1:0] buf_invalid_alloc;
  logic [NumBuf-1:0] buf_valid_alloc;
  logic [NumBuf-1:0] buf_alloc;

  for (genvar i = 0; i < NumBuf; i++) begin: gen_buf_states
    assign buf_valid[i]   = read_buf[i].attr == Valid;
    assign buf_wip[i]     = read_buf[i].attr == Wip;
    assign buf_invalid[i] = read_buf[i].attr == Invalid;
  end

  assign buf_invalid_alloc[0] = buf_invalid[0];
  for (genvar i = 1; i < NumBuf; i++) begin: gen_inv_alloc_bufs
    assign buf_invalid_alloc[i] = buf_invalid[i] & ~|buf_invalid_alloc[i-1:0];
  end

  // a prim arbiter is used to somewhat fairly select among the valid buffers
  logic [1:0] dummy_data [NumBuf];
  for (genvar i = 0; i < NumBuf; i++) begin: gen_dummy
    assign dummy_data[i] = '0;
  end

  // using prim arbiter tree since it supports per cycle arbitration instead of
  // winner lock
  prim_arbiter_tree #(
    .N(NumBuf),
    .Lock(0),
    .DW(2)
  ) i_valid_random (
    .clk_i,
    .rst_ni,
    .req_i(buf_valid),
    .data_i(dummy_data),
    .gnt_o(buf_valid_alloc),
    .idx_o(),
    .valid_o(),
    .data_o(),
    .ready_i(req_i & rdy_o)
  );

  // which buffer to allocate upon a new transaction
  assign buf_alloc = |buf_invalid_alloc ? buf_invalid_alloc : buf_valid_alloc;

  // do not attempt to generate match unless the transaction is relevant
  for (genvar i = 0; i < NumBuf; i++) begin: gen_buf_match
    assign buf_match[i] = req_i & (buf_valid[i] | buf_wip[i]) &
                          read_buf[i].addr == addr_i[BankAddrW-1:LsbAddrBit];

    // A data hazard should never happen to a wip buffer because it implies
    // that a read is in progress, so a hazard operation cannot start.
    // If bank erase, all buffers must be flushed.
    // If page erase, only if the buffer lands in the same page.
    // If program, only if it's the same flash word.
    assign data_hazard[i] = buf_valid[i] &
                            (bk_erase_i |
                            (prog_i & read_buf[i].addr == addr_i[BankAddrW-1:LsbAddrBit]) |
                            (pg_erase_i & read_buf[i].addr[FlashWordsW +: PageW] ==
                            addr_i[WordW +: PageW]));

  end

  assign no_match = ~|buf_match;

  // if new request does not match anything, allocate
  assign alloc = no_match ? {NumBuf{req_i}} &  buf_alloc : '0;

  // read buffers
  // allocate sets state to Wip
  // update sets state to valid
  // wipe sets state to invalid - this comes from prog
  for (genvar i = 0; i < NumBuf; i++) begin: gen_bufs
    flash_phy_rd_buffers i_rd_buf (
      .clk_i,
      .rst_ni,
      .alloc_i(rdy_o & alloc[i]),
      .update_i(update[i]),
      .wipe_i(data_hazard[i]),
      .addr_i(addr_i[BankAddrW-1:LsbAddrBit]),
      .data_i(data_i),
      .out_o(read_buf[i])
    );
  end

  /////////////////////////////////
  // Flash read stage
  /////////////////////////////////

  // Flash read stage determines if the transactions are accepted.
  //
  // The response fifo is written to when a transaction initiates a flash read OR when a match
  // is hit. The information written is just the allocated buffer that would have satisifed the
  // transaction, as well as bits that indiate which part of the buffer is the right return data
  //
  // This allows a hit transaction to match in-order, and unblock later transactions to begin
  // reading from the flash primitive

  rsp_fifo_entry_t rsp_fifo_wdata, rsp_fifo_rdata;
  logic rsp_fifo_rdy;
  logic rsp_fifo_vld;

  // whether there is an ongoing read to flash
  // stage is idle when a transaction is ongoing, and the cycle when a response comes from
  // the flash primitive
  logic rd_stage_idle;
  logic rd_busy;
  logic rd_done;
  logic [NumBuf-1:0] alloc_q;

  assign rd_done = rd_busy & ack_i;

  // if buffer allocated, that is the return source
  // if buffer matched, that is the return source
  assign rsp_fifo_wdata.buf_sel = |alloc ? buf_alloc : buf_match;

  // If width is the same, word_sel is unused
  if (WidthMultiple == 1) begin : gen_single_word_sel
    assign rsp_fifo_wdata.word_sel = '0;
  end else begin : gen_word_sel
    assign rsp_fifo_wdata.word_sel = addr_i[0 +: LsbAddrBit];
  end

  // response order FIFO
  prim_fifo_sync #(
      .Width  (RspOrderFifoWidth),
      .Pass   (0),
      .Depth  (RspOrderDepth)
  ) i_rsp_order_fifo (
    .clk_i,
    .rst_ni,
    .clr_i  (1'b0),
    .wvalid (req_i && rdy_o),
    .wready (rsp_fifo_rdy),
    .wdata  (rsp_fifo_wdata),
    .depth  (),
    .rvalid (rsp_fifo_vld),
    .rready (data_valid_o), // pop when a match has been found
    .rdata  (rsp_fifo_rdata)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_busy <= 1'b0;
      alloc_q <= '0;
    end else if (req_o) begin
      // read only becomes busy if a buffer is allocated and read
      rd_busy <= 1'b1;
      alloc_q <= alloc;
    end else if (rd_done) begin
      rd_busy <= 1'b0;
    end
  end

  // this stage is idle whenever there is not an ongoing read, or if there is
  // but the ack has returned
  assign rd_stage_idle = !rd_busy | ack_i;

  // if no buffers matched, accept only if read state is idle and there is space
  // if buffer is matched, accept as long as there is space in the rsp fifo
  assign rdy_o = no_match ? rd_stage_idle & rsp_fifo_rdy : rsp_fifo_rdy;

  // issue a transaction to flash
  assign req_o = req_i & rdy_o & no_match;

  /////////////////////////////////
  // De-scrambling stage
  /////////////////////////////////

  // nothing here yet


  /////////////////////////////////
  // Response
  /////////////////////////////////

  logic flash_rsp_match;
  logic [NumBuf-1:0] buf_rsp_match;
  logic [DataWidth-1:0] buf_rsp_data;

  // update buffers
  assign update = rd_done ? alloc_q : '0;

  // match in flash response when allocated buffer is the same as top of response fifo
  assign flash_rsp_match = rsp_fifo_vld & rd_done & (rsp_fifo_rdata.buf_sel == alloc_q);

  // match in buf response when there is a valie buffer that is the same as top of response fifo
  for (genvar i = 0; i < NumBuf; i++) begin: gen_buf_rsp_match
    assign buf_rsp_match[i] = rsp_fifo_vld & (rsp_fifo_rdata.buf_sel[i] & buf_valid[i]);
  end

  // select among the buffers
  always_comb begin
    buf_rsp_data = data_i;
    for (int i = 0; i < NumBuf; i++) begin
      if (buf_rsp_match[i]) begin
        buf_rsp_data = read_buf[i].data;
      end
    end
  end

  if (WidthMultiple == 1) begin : gen_width_one_rd
    // When multiple is 1, just pass the read through directly
    logic unused_word_sel;
    assign data_o = |buf_rsp_match ? buf_rsp_data : data_i;
    assign unused_word_sel = rsp_fifo_rdata.word_sel;

  end else begin : gen_rd
    // Re-arrange data into packed array to pick the correct one
    logic [WidthMultiple-1:0][BusWidth-1:0] bus_words_packed;
    assign bus_words_packed = |buf_rsp_match ? buf_rsp_data : data_i;
    assign data_o = bus_words_packed[rsp_fifo_rdata.word_sel];

  end

  assign data_valid_o = flash_rsp_match | |buf_rsp_match;


  // the entire read pipeline is idle when there are no responses to return
  assign idle_o = ~rsp_fifo_vld;

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // The buffers are flip flop based, do not allow too many of them
  `ASSERT_INIT(MaxBufs_A, NumBuf <= 8)

  // match should happen only to 1 buffer
  `ASSERT(OneHotMatch_A, $onehot0(buf_match))

  // allocate should happen only to 1 buffer at time
  `ASSERT(OneHotAlloc_A, $onehot0(alloc))

  // update should happen only to 1 buffer at time
  `ASSERT(OneHotUpdate_A, $onehot0(update))

  // alloc and update should be mutually exclusive for a buffer
  `ASSERT(ExclusiveOps_A, (alloc & update) == 0 )

  // valid and wip are mutually exclusive
  `ASSERT(ExclusiveState_A, (buf_valid & buf_wip) == 0)

  // data_hazard and wip should be mutually exclusive
  `ASSERT(ExclusiveProgHazard_A, (data_hazard & buf_wip) == 0)

  // unless the pipeline is idle, we should not have non-read trasnactions
  `ASSERT(IdleCheck_A, !idle_o |-> {prog_i,pg_erase_i,bk_erase_i} == '0)


endmodule // flash_phy_core
