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
// or forwarded directly to the buffer (no de-scramble)
//
// If the storage element between read and de-scramble stages are completely full
// for any reason, then the read stage cannot start.
//
// When the read stage begins, the galois multiply portion of the de-scramble is
// also kicked off. When the galois multiply stage AND read stage completes, the
// de-scramble is then kicked off.

module flash_phy_rd import flash_phy_pkg::*; (
  input clk_i,
  input rst_ni,

  // configuration interface from flash controller
  input buf_en_i,

  // interface with arbitration unit
  input req_i,
  input descramble_i,
  input ecc_i,
  input prog_i,
  input pg_erase_i,
  input bk_erase_i,
  input [BusBankAddrW-1:0] addr_i,
  input flash_ctrl_pkg::flash_part_e part_i,
  input [InfoTypesWidth-1:0] info_sel_i,
  output logic rdy_o,
  output logic data_valid_o,
  output logic data_err_o,
  output logic [BusWidth-1:0] data_o,
  output logic idle_o, // the entire read pipeline is idle

  // interface with scramble unit
  output logic calc_req_o,
  output logic descramble_req_o,
  output logic [BankAddrW-1:0] calc_addr_o,
  output logic [DataWidth-1:0] scrambled_data_o,
  input calc_ack_i,
  input descramble_ack_i,
  input [DataWidth-1:0] mask_i,
  input [DataWidth-1:0] descrambled_data_i,

  // interface to actual flash primitive
  output logic req_o,
  input ack_i,  // request has been accepted
  input done_i, // actual data return
  input [FullDataWidth-1:0] data_i,

  // error status reporting
  output logic ecc_single_err_o,
  output logic ecc_multi_err_o,
  output logic [BusBankAddrW-1:0] ecc_addr_o
  );

  /////////////////////////////////
  // Read buffers
  /////////////////////////////////

  // internal buffer enable
  logic buf_en_q;

  // muxed de-scrambled and plain-data
  logic [DataWidth-1:0] muxed_data;
  logic muxed_err;

  // muxed data valid signal that takes scrambling into consideration
  logic data_valid;

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

  // flash word address
  logic [BankAddrW-1:0] flash_word_addr;
  assign flash_word_addr = addr_i[BusBankAddrW-1:LsbAddrBit];

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

  prim_arbiter_tree #(
    .N(NumBuf),
    // disable request stability assertion
    .EnReqStabA(0),
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
    .ready_i(req_o)
  );

  // which buffer to allocate upon a new transaction
  assign buf_alloc = |buf_invalid_alloc ? buf_invalid_alloc : buf_valid_alloc;

  // do not attempt to generate match unless the transaction is relevant
  for (genvar i = 0; i < NumBuf; i++) begin: gen_buf_match
    logic part_match;
    logic info_sel_match;

    assign part_match = read_buf[i].part == part_i;
    assign info_sel_match = read_buf[i].info_sel == info_sel_i;

    assign buf_match[i] = req_i &
                          buf_en_q &
                          (buf_valid[i] | buf_wip[i]) &
                          (read_buf[i].addr == flash_word_addr) &
                          part_match &
                          info_sel_match;

    // A data hazard should never happen to a wip buffer because it implies
    // that a read is in progress, so a hazard operation cannot start.
    // If bank erase, all buffers must be flushed.
    // If page erase, only if the buffer lands in the same page.
    // If program, only if it's the same flash word.
    logic word_addr_match;
    logic page_addr_match;

    assign word_addr_match = (read_buf[i].addr == flash_word_addr) &
                             part_match &
                             info_sel_match;

    // the read buffer address in on flash word boundary
    // while the incoming address in on the bus word boundary
    assign page_addr_match = (read_buf[i].addr[WordW +: PageW] == addr_i[BusWordW +: PageW]) &
                             part_match &
                             info_sel_match;

    assign data_hazard[i] = buf_valid[i] &
                            (bk_erase_i |
                            (prog_i & word_addr_match) |
                            (pg_erase_i & page_addr_match));

  end

  assign no_match = ~|buf_match;

  // if new request does not match anything, allocate
  assign alloc = no_match ? {NumBuf{req_i & buf_en_q}} &  buf_alloc : '0;

  // read buffers
  // allocate sets state to Wip
  // update sets state to valid
  // wipe sets state to invalid - this comes from prog
  for (genvar i = 0; i < NumBuf; i++) begin: gen_bufs
    flash_phy_rd_buffers u_rd_buf (
      .clk_i,
      .rst_ni,
      .en_i(buf_en_q),
      .alloc_i(rdy_o & alloc[i]),
      .update_i(update[i] & ~muxed_err),
      .wipe_i(data_hazard[i]),
      .addr_i(flash_word_addr),
      .part_i(part_i),
      .info_sel_i(info_sel_i),
      .data_i(muxed_data),
      .out_o(read_buf[i])
    );
  end

  // buffer enable cannot be changed unless the entire read pipeline is idle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      buf_en_q <= 1'b0;
    end else if (idle_o) begin
      buf_en_q <= buf_en_i;
    end
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

  // saved attributes on flash read
  logic [NumBuf-1:0] alloc_q;
  rd_attr_t rd_attrs;

  // read complete
  // since done is broadcast to all the modules, need to know we are actually active
  logic rd_busy;
  logic rd_done;

  assign rd_done = rd_busy & done_i;

  // scramble stage ready
  logic scramble_stage_rdy;

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
    .clr_i   (1'b0),
    .wvalid_i(req_i && rdy_o),
    .wready_o(rsp_fifo_rdy),
    .wdata_i (rsp_fifo_wdata),
    .depth_o (),
    .full_o (),
    .rvalid_o(rsp_fifo_vld),
    .rready_i(data_valid_o), // pop when a match has been found
    .rdata_o (rsp_fifo_rdata)
  );


  // Consider converting this to a FIFO for better matching
  // The rd_busy flag is effectively a "full" flag anyways of a single
  // entry.
  logic flash_rdy;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      alloc_q <= '0;
      rd_attrs <= '0;
      rd_busy <= '0;
    end else if (req_o && ack_i) begin
      rd_busy <= 1'b1;
      alloc_q <= alloc;
      rd_attrs.addr <= addr_i[BusBankAddrW-1:LsbAddrBit];
      rd_attrs.descramble <= descramble_i;
      rd_attrs.ecc <= ecc_i;
    end else if (rd_done) begin
      rd_busy <= 1'b0;
    end
  end

  // flash is ready to accept another transaction
  assign flash_rdy = ~rd_busy | rd_done;

  // read stages are ready when both the response fifo and the
  // data / mask fifos have space for new entries
  logic rd_stages_rdy;
  assign rd_stages_rdy = rsp_fifo_rdy & scramble_stage_rdy;

  // if no buffers matched, accept only if flash is ready and there is space
  // if buffer is matched, accept as long as there is space in the rsp fifo
  assign rdy_o = no_match ? ack_i & flash_rdy & rd_stages_rdy : rd_stages_rdy;

  // issue a transaction to flash only if there is space in read stages,
  // there is no buffer match and flash is not currently busy.
  assign req_o = req_i & flash_rdy & rd_stages_rdy & no_match;

  /////////////////////////////////
  // Handling ECC
  /////////////////////////////////

  // only uncorrectable errors are passed on to the fabric
  logic data_err;

  // scrambled data must pass through ECC first
  logic valid_ecc;
  logic ecc_multi_err;
  logic ecc_single_err;
  logic [DataWidth-1:0] data_ecc_chk;
  logic [DataWidth-1:0] data_int;
  logic data_erased;

  assign valid_ecc = rd_done && rd_attrs.ecc && !data_erased;

  // When all bits are 1, the data has been erased
  // This check is only valid when read data returns.
  assign data_erased = rd_done & (data_i == {FullDataWidth{1'b1}});

  prim_secded_hamming_72_64_dec u_dec (
    .in(data_i[ScrDataWidth-1:0]),
    .d_o(data_ecc_chk),
    .syndrome_o(),
    .err_o({ecc_multi_err, ecc_single_err})
  );

  // If data needs to be de-scrambled and has not been erased, pass through ecc decoder.
  // Otherwise, pass the data through untouched.
  // Likewise, ecc error is only observed if the data needs to be de-scrambled and has not been
  // erased.
  // rd_done signal below is duplicated (already in data_erased) to show clear intent of the code.
  assign data_int = valid_ecc ? data_ecc_chk :
                                data_i[DataWidth-1:0];
  assign data_err = valid_ecc & ecc_multi_err;
  assign ecc_multi_err_o = data_err;
  assign ecc_single_err_o = valid_ecc & ecc_single_err;
  // ecc address return is always the full flash word
  assign ecc_addr_o = {rd_attrs.addr, {LsbAddrBit{1'b0}}};

  /////////////////////////////////
  // De-scrambling stage
  /////////////////////////////////

  // Even on ECC error, progress through the stage normally

  logic fifo_data_ready;
  logic fifo_data_valid;
  logic mask_valid;
  logic [DataWidth-1:0] fifo_data;
  logic [DataWidth-1:0] mask;
  logic data_fifo_rdy;
  logic mask_fifo_rdy;
  logic descram;
  logic forward;
  logic hint_forward;
  logic hint_descram;
  logic data_err_q;
  logic [NumBuf-1:0] alloc_q2;

  assign scramble_stage_rdy = data_fifo_rdy & mask_fifo_rdy;

  // data is consumed when:
  // 1. When descrambling completes
  // 2. Immediately consumed when descrambling not required
  // 3. In both cases, when data has not already been forwarded
  assign fifo_data_ready = hint_descram ? descramble_req_o & descramble_ack_i :
                                          fifo_data_valid;

  // descramble is only required if the location is scramble enabled AND it is not erased.
  assign descram = rd_done & rd_attrs.descramble & ~data_erased;

  // data is forwarded whenever it does not require descrambling and there are no entries in the
  // FIFO to ensure the current read cannot run ahead of the descramble.
  assign forward = rd_done & ~descram & ~fifo_data_valid;

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
  logic fifo_forward_pop;
  assign fifo_forward_pop = hint_forward & fifo_data_valid;

  prim_fifo_sync #(
    .Width   (DataWidth + 3 + NumBuf),
    .Pass    (0),
    .Depth   (2),
    .OutputZeroIfEmpty (1)
  ) u_rd_storage (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(rd_done),
    .wready_o(data_fifo_rdy),
    .wdata_i ({alloc_q, descram, forward, data_err, data_int}),
    .depth_o (),
    .full_o (),
    .rvalid_o(fifo_data_valid),
    .rready_i(fifo_data_ready | fifo_forward_pop),
    .rdata_o ({alloc_q2, hint_descram, hint_forward, data_err_q, fifo_data})
  );

  // storage for mask calculations
  prim_fifo_sync #(
    .Width   (DataWidth),
    .Pass    (0),
    .Depth   (2),
    .OutputZeroIfEmpty (1)
  ) u_mask_storage (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(calc_req_o & calc_ack_i),
    .wready_o(mask_fifo_rdy),
    .wdata_i (mask_i),
    .depth_o (),
    .full_o (),
    .rvalid_o(mask_valid),
    .rready_i(fifo_data_ready | fifo_forward_pop),
    .rdata_o (mask)
  );

  // generate the mask calculation request
  // mask calculation is done in parallel to the read stage
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
  assign descramble_req_o = fifo_data_valid & mask_valid & hint_descram;

  // scrambled data to de-scramble
  assign scrambled_data_o = fifo_data ^ mask;

  // muxed responses
  // When "forward" is true, there is nothing ahead in the pipeline, directly feed data
  // and error forward.
  // When "forward" is not true, take the output from the descrmable stage, which is
  // dependent on the scramble hint.
  assign muxed_data = forward      ? data_int :
                      hint_descram ? descrambled_data_i ^ mask : fifo_data;
  assign muxed_err  = forward      ? data_err : data_err_q;

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
  assign update = forward         ? alloc_q  :
                  fifo_data_ready ? alloc_q2 : '0;

  // match in flash response when allocated buffer is the same as top of response fifo
  // if read buffers are not enabled, do not check buffer selection
  assign flash_rsp_match = rsp_fifo_vld & data_valid &
                           (~buf_en_q | rsp_fifo_rdata.buf_sel == update);

  // match in buf response when there is a valid buffer that is the same as top of response fifo
  for (genvar i = 0; i < NumBuf; i++) begin: gen_buf_rsp_match
    assign buf_rsp_match[i] = buf_en_q & rsp_fifo_vld &
                              (rsp_fifo_rdata.buf_sel[i] & buf_valid[i]);
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
    assign data_o = data_err_o     ? {BusWidth{1'b1}} :
                    |buf_rsp_match ? buf_rsp_data : muxed_data;
    assign unused_word_sel = rsp_fifo_rdata.word_sel;

  end else begin : gen_rd
    // Re-arrange data into packed array to pick the correct one
    logic [WidthMultiple-1:0][BusWidth-1:0] bus_words_packed;
    assign bus_words_packed = |buf_rsp_match ? buf_rsp_data : muxed_data;
    assign data_o = data_err_o ? {BusWidth{1'b1}} : bus_words_packed[rsp_fifo_rdata.word_sel];

  end

  // whenever the response is coming from the buffer, the error is never set
  assign data_valid_o = flash_rsp_match | |buf_rsp_match;
  assign data_err_o   = muxed_err;

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
  `ASSERT(ExclusiveOps_A, (alloc & update) == 0 )

  // valid and wip are mutually exclusive
  `ASSERT(ExclusiveState_A, (buf_valid & buf_wip) == 0)

  // data_hazard and wip should be mutually exclusive
  `ASSERT(ExclusiveProgHazard_A, (data_hazard & buf_wip) == 0)

  // unless the pipeline is idle, we should not have non-read trasnactions
  `ASSERT(IdleCheck_A, !idle_o |-> {prog_i,pg_erase_i,bk_erase_i} == '0)

  // Whenever forward is true, hint_descram should always be 0
  `ASSERT(ForwardCheck_A, forward |-> hint_descram == '0)

  // Whenever response is coming from buffer, ecc error cannot be set
  `ASSERT(BufferMatchEcc_A, |buf_rsp_match |-> muxed_err == '0)

  /////////////////////////////////
  // Functional coverage points to add
  /////////////////////////////////

  // exercise both flash_read and de-scramble stages at the same time
  // - make sure accesses can be consecutive or random
  // exercise back to back transactions, and transactions with varying delays
  // exercise data hazard where erase / program requires buffer eviction

endmodule // flash_phy_core
