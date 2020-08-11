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
//
// Support for descramble stage
// The allocate and descramble indication received at read stage are saved.
// When the read completes, depending on the 'descramble' indication saved, the
// data is either stored into FIFO (reg + skid) between read and descramble stage,
// or forwarded directly to the buffers (no de-scramble)
//
// If the storage element between read and de-scramble stages are completely full
// for any reason, then the read stage cannot start.
//
// When the read stage begins, the galois multiply portion of the de-scramble is
// also be kicked off. When the galois multiply stage AND read stage completes, the
// de-scramble is then kicked off.

module flash_phy_rd
import flash_phy_pkg::*;
(
    input clk_i,
    input rst_ni,

    // interface with arbitration unit
    input req_i,
    input descramble_i,
    input prog_i,
    input pg_erase_i,
    input bk_erase_i,
    input [BusBankAddrW-1:0] addr_i,
    input flash_ctrl_pkg::flash_part_e part_i,
    output logic rdy_o,
    output logic data_valid_o,
    output logic [BusWidth-1:0] data_o,
    output logic idle_o,  // the entire read pipeline is idle

    // interface with scramble unit
    output logic                 calc_req_o,
    output logic                 descramble_req_o,
    output logic [BankAddrW-1:0] calc_addr_o,
    output logic [DataWidth-1:0] scrambled_data_o,
    input                        calc_ack_i,
    input                        descramble_ack_i,
    input        [DataWidth-1:0] mask_i,
    input        [DataWidth-1:0] descrambled_data_i,

    // interface to actual flash primitive
    output logic                 req_o,
    input                        ack_i,
    input        [DataWidth-1:0] data_i
);

  /////////////////////////////////
  // Read buffers
  /////////////////////////////////

  // muxed de-scrambled and plain-data
  logic [DataWidth-1:0] muxed_data;

  // muxed data valid signal that takes scrambling into consideration
  logic data_valid;

  // A buffer allocate is invoked when a new transaction arrives.
  // Alloc only happens if the new transaction does not match an existing entry.
  logic [NumBuf-1:0] alloc;

  // A buffer update is invoked after the completion of the de-scramble stage.
  // This updates the buffer that was allocated when a new transaction was initiated.
  logic [NumBuf-1:0] update;

  rd_buf_t read_buf[NumBuf];
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

  // flash word address
  logic [BankAddrW-1:0] flash_word_addr;
  assign flash_word_addr = addr_i[BusBankAddrW - 1:LsbAddrBit];

  for (genvar i = 0; i < NumBuf; i++) begin : gen_buf_states
    assign buf_valid[i] = read_buf[i].attr == Valid;
    assign buf_wip[i] = read_buf[i].attr == Wip;
    assign buf_invalid[i] = read_buf[i].attr == Invalid;
  end

  assign buf_invalid_alloc[0] = buf_invalid[0];
  for (genvar i = 1; i < NumBuf; i++) begin : gen_inv_alloc_bufs
    assign buf_invalid_alloc[i] = buf_invalid[i] & ~|buf_invalid_alloc[i - 1:0];
  end

  // a prim arbiter is used to somewhat fairly select among the valid buffers
  logic [1:0] dummy_data[NumBuf];
  for (genvar i = 0; i < NumBuf; i++) begin : gen_dummy
    assign dummy_data[i] = '0;
  end

  prim_arbiter_tree #(
      .N(NumBuf),
      // disable request stability assertion
      .EnReqStabA(0),
      .DW(2)
  ) i_valid_random (
      .clk_i,
      .rst_ni,
      .req_i  (buf_valid),
      .data_i (dummy_data),
      .gnt_o  (buf_valid_alloc),
      .idx_o  (),
      .valid_o(),
      .data_o (),
      .ready_i(req_o)
  );

  // which buffer to allocate upon a new transaction
  assign buf_alloc = |buf_invalid_alloc ? buf_invalid_alloc : buf_valid_alloc;

  // do not attempt to generate match unless the transaction is relevant
  for (genvar i = 0; i < NumBuf; i++) begin : gen_buf_match
    assign buf_match[i] = req_i & (buf_valid[i] | buf_wip[i]) & (read_buf[i].addr == flash_word_addr
        ) & (read_buf[i].part == part_i);

    // A data hazard should never happen to a wip buffer because it implies
    // that a read is in progress, so a hazard operation cannot start.
    // If bank erase, all buffers must be flushed.
    // If page erase, only if the buffer lands in the same page.
    // If program, only if it's the same flash word.

    logic part_match;
    logic word_addr_match;
    logic page_addr_match;

    assign part_match = read_buf[i].part == part_i;
    assign word_addr_match = (read_buf[i].addr == flash_word_addr) & part_match;

    // the read buffer address in on flash word boundary
    // while the incoming address in on the bus word boundary
    assign page_addr_match = (read_buf[i].addr[WordW +: PageW] == addr_i[BusWordW +: PageW]) &
        part_match;

    assign data_hazard[i] =
        buf_valid[i] & (bk_erase_i | (prog_i & word_addr_match) | (pg_erase_i & page_addr_match));

  end

  assign no_match = ~|buf_match;

  // if new request does not match anything, allocate
  assign alloc = no_match ? {NumBuf{req_i}} & buf_alloc : '0;

  // read buffers
  // allocate sets state to Wip
  // update sets state to valid
  // wipe sets state to invalid - this comes from prog
  for (genvar i = 0; i < NumBuf; i++) begin : gen_bufs
    flash_phy_rd_buffers u_rd_buf (
        .clk_i,
        .rst_ni,
        .alloc_i (rdy_o & alloc[i]),
        .update_i(update[i]),
        .wipe_i  (data_hazard[i]),
        .addr_i  (flash_word_addr),
        .part_i  (part_i),
        .data_i  (muxed_data),
        .out_o   (read_buf[i])
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
  rd_attr_t rd_attrs;

  // scramble stage ready
  logic scramble_stage_rdy;

  // read done does not mean data is available.
  // if the data must be de-scrambled, there is another wait stage
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
      .Width(RspOrderFifoWidth),
      .Pass(0),
      .Depth(RspOrderDepth)
  ) i_rsp_order_fifo (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(req_i && rdy_o),
      .wready_o(rsp_fifo_rdy),
      .wdata_i (rsp_fifo_wdata),
      .depth_o (),
      .rvalid_o(rsp_fifo_vld),
      .rready_i(data_valid_o),  // pop when a match has been found
      .rdata_o (rsp_fifo_rdata)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_busy <= 1'b0;
      alloc_q <= '0;
      rd_attrs <= '0;
    end else if (req_o) begin
      // read only becomes busy if a buffer is allocated and read
      rd_busy <= 1'b1;
      alloc_q <= alloc;
      rd_attrs.addr <= addr_i[BusBankAddrW - 1:LsbAddrBit];
      rd_attrs.descramble <= descramble_i;
    end else if (rd_done) begin
      rd_busy <= 1'b0;
    end
  end

  // this stage is idle whenever there is not an ongoing read, or if there is
  // but the ack has returned
  assign rd_stage_idle = !rd_busy | ack_i;

  // if no buffers matched, accept only if read state is idle and there is space
  // if buffer is matched, accept as long as there is space in the rsp fifo
  assign rdy_o = no_match ? rd_stage_idle & rsp_fifo_rdy & scramble_stage_rdy :
      rsp_fifo_rdy & scramble_stage_rdy;

  // issue a transaction to flash
  assign req_o = req_i & rdy_o & no_match;

  /////////////////////////////////
  // De-scrambling stage
  /////////////////////////////////

  logic fifo_data_ready;
  logic fifo_data_valid;
  logic mask_valid;
  logic [DataWidth-1:0] fifo_data;
  logic [DataWidth-1:0] mask;
  logic data_fifo_rdy;
  logic mask_fifo_rdy;
  logic forward;
  logic hint_forward;
  logic hint_descram;
  logic [NumBuf-1:0] alloc_q2;

  assign scramble_stage_rdy = data_fifo_rdy & mask_fifo_rdy;

  // data is consumed when:
  // 1. When descrambling completes
  // 2. Immediately consumed when descrambling not required
  // 3. In both cases, when data has not already been forwarded
  assign fifo_data_ready = hint_descram ? descramble_req_o & descramble_ack_i & ~hint_forward :
      fifo_data_valid & !hint_forward;

  // data is forwarded whenever it does not require descrambling or if it has been erased
  // but forwarding is only possible if there are no entries in the FIFO to ensure the current
  // read cannot run ahead of the descramble.
  assign
      forward = rd_done & !fifo_data_valid & ((data_i == {DataWidth{1'b1}}) | !rd_attrs.descramble);

  // storage for read outputs
  // This storage element can be fully merged with the fifo below if the time it takes
  // to do a read is matched to gf_mult.  This is doable and should be considered.
  // However it would create a dependency on constraints (multicycle) instead of
  // being correct by construction.
  //
  // In addition to potential different completion times, the mask storage may also
  // be pushed even if it is not required (erase case). The solution for this issue
  // is that the mask / data are always pushed, it is then selectively popped based
  // on the forward / de-scrambling hints.
  //
  // All these problems could be resolved if the timings matched exactly, however
  // the user would need to correctly setup constraints on either flash / gf_mult
  // timing change.
  prim_fifo_sync #(
      .Width(DataWidth + 2 + NumBuf),
      .Pass(0),
      .Depth(2)
  ) u_rd_storage (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(rd_done),
      .wready_o(data_fifo_rdy),
      .wdata_i ({alloc_q, rd_attrs.descramble, forward, data_i}),
      .depth_o (),
      .rvalid_o(fifo_data_valid),
      .rready_i(fifo_data_ready | hint_forward),
      .rdata_o ({alloc_q2, hint_descram, hint_forward, fifo_data})
  );

  // storage for mask calculations
  prim_fifo_sync #(
      .Width(DataWidth),
      .Pass(0),
      .Depth(2)
  ) u_mask_storage (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(calc_req_o & calc_ack_i),
      .wready_o(mask_fifo_rdy),
      .wdata_i (mask_i),
      .depth_o (),
      .rvalid_o(mask_valid),
      .rready_i(fifo_data_ready | hint_forward),
      .rdata_o (mask)
  );

  // generate the mask calculation request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      calc_req_o <= '0;
    end else if (req_o && descramble_i) begin
      calc_req_o <= 1'b1;
    end else if (calc_req_o && calc_ack_i) begin
      calc_req_o <= 1'b0;
    end
  end

  // operand to gf_mult
  assign calc_addr_o = rd_attrs.addr;

  // generate the descramble request whenever both stages are available
  // and there is a need to descramble
  assign descramble_req_o = fifo_data_valid & mask_valid & !hint_forward;

  // scrambled data to de-scramble
  assign scrambled_data_o = fifo_data ^ mask;

  // muxed data
  assign muxed_data = hint_descram ? descrambled_data_i ^ mask : data_i;

  // muxed data valid
  // if no de-scramble required, return data on read complete
  // if data is all empty (erased), also return data on read complete
  // if descramble is required, return data when descrambler finishes
  assign data_valid = forward | fifo_data_ready;


  /////////////////////////////////
  // Response
  /////////////////////////////////

  logic flash_rsp_match;
  logic [NumBuf-1:0] buf_rsp_match;
  logic [DataWidth-1:0] buf_rsp_data;

  // update buffers
  // When forwarding, update entry stored in alloc_q
  // When de-scrambling however, the contents of alloc_q may have already updated to the next read,
  // so a different pointer is used.
  // assign update = data_valid ? alloc_q : '0;
  assign update = forward ? alloc_q : fifo_data_ready ? alloc_q2 : '0;

  // match in flash response when allocated buffer is the same as top of response fifo
  assign flash_rsp_match = rsp_fifo_vld & data_valid & (rsp_fifo_rdata.buf_sel == update);

  // match in buf response when there is a valid buffer that is the same as top of response fifo
  for (genvar i = 0; i < NumBuf; i++) begin : gen_buf_rsp_match
    assign buf_rsp_match[i] = rsp_fifo_vld & (rsp_fifo_rdata.buf_sel[i] & buf_valid[i]);
  end

  // select among the buffers
  always_comb begin
    buf_rsp_data = muxed_data;
    for (int i = 0; i < NumBuf; i++) begin
      if (buf_rsp_match[i]) begin
        buf_rsp_data = read_buf[i].data;
      end
    end
  end

  if (WidthMultiple == 1) begin : gen_width_one_rd
    // When multiple is 1, just pass the read through directly
    logic unused_word_sel;
    assign data_o = |buf_rsp_match ? buf_rsp_data : muxed_data;
    assign unused_word_sel = rsp_fifo_rdata.word_sel;

  end else begin : gen_rd
    // Re-arrange data into packed array to pick the correct one
    logic [WidthMultiple-1:0][BusWidth-1:0] bus_words_packed;
    assign bus_words_packed = |buf_rsp_match ? buf_rsp_data : muxed_data;
    assign data_o = bus_words_packed[rsp_fifo_rdata.word_sel];

  end

  assign data_valid_o = flash_rsp_match | |buf_rsp_match;

  // the entire read pipeline is idle when there are no responses to return and no
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
  `ASSERT(ExclusiveOps_A, (alloc & update) == 0)

  // valid and wip are mutually exclusive
  `ASSERT(ExclusiveState_A, (buf_valid & buf_wip) == 0)

  // data_hazard and wip should be mutually exclusive
  `ASSERT(ExclusiveProgHazard_A, (data_hazard & buf_wip) == 0)

  // unless the pipeline is idle, we should not have non-read trasnactions
  `ASSERT(IdleCheck_A, !idle_o |-> {prog_i, pg_erase_i, bk_erase_i} == '0)


endmodule  // flash_phy_core
