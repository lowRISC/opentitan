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

module flash_phy_rd
  import flash_phy_pkg::*;
  import prim_mubi_pkg::mubi4_t;
(
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
  output logic relbl_ecc_err_o,
  output logic intg_ecc_err_o,
  output logic [BusFullWidth-1:0] data_o,
  output logic idle_o, // the entire read pipeline is idle
  input arb_err_i, // a catastrophic arbitration error was observed

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
  // only single bit error is shown here as multi-bit errors are
  // actual data errors and reflected in-band through data_err_o
  output logic ecc_single_err_o,
  output logic [BusBankAddrW-1:0] ecc_addr_o,

  // fifo error
  output logic fifo_err_o
  );

  /////////////////////////////////
  // Read buffers
  /////////////////////////////////

  // internal buffer enable
  logic buf_en_q;

  // muxed de-scrambled and plain-data
  logic [PlainDataWidth-1:0] muxed_data;
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

  // This net tracks which buffers have a dependency to items currently in the rsp_order_fifo
  logic [NumBuf-1:0] buf_dependency;

  // all buffers have a current dependency to an entry in rsp_order_fifo
  logic all_buf_dependency;

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

    // if a buffer is valid and contains an error, it should be considered
    // invalid as long as there are no pending responses already waiting
    // on that buffer.
    assign buf_invalid[i] = (read_buf[i].attr == Invalid) |
                            (read_buf[i].attr == Valid &
                            read_buf[i].err &
                            ~buf_dependency[i]);
  end

  assign buf_invalid_alloc[0] = buf_invalid[0];
  for (genvar i = 1; i < NumBuf; i++) begin: gen_inv_alloc_bufs
    assign buf_invalid_alloc[i] = buf_invalid[i] & ~|buf_invalid[i-1:0];
  end

  // a prim arbiter is used to somewhat fairly select among the valid buffers
  logic [1:0] dummy_data [NumBuf];
  for (genvar i = 0; i < NumBuf; i++) begin: gen_dummy
    assign dummy_data[i] = '0;
  end

  prim_arbiter_tree #(
    .N(NumBuf),
    .DW(2),
    .EnDataPort(1'b0)
  ) u_valid_random (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b0), // Valid is allowed to drop without ready.
    // If there is an invalid buffer, always allocate from that one first
    // If all buffers have a dependency to an in-flight transaction, do not
    // allocate and wait for the dependencies to end.
    // If none of the above are true, THEN pick a buffer from the current valid
    // buffers that DO NOT have an ongoing dependency.
    .req_i(|buf_invalid_alloc | all_buf_dependency ? '0 : buf_valid & ~buf_dependency),
    .data_i(dummy_data),
    .gnt_o(buf_valid_alloc),
    .idx_o(),
    .valid_o(),
    .data_o(),
    .ready_i(req_o & no_match)
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
                          ~read_buf[i].err &
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
      .update_i(update[i]),
      .err_i(muxed_err),
      .wipe_i(data_hazard[i]),
      .addr_i(flash_word_addr),
      .part_i(part_i),
      .info_sel_i(info_sel_i),
      .data_i(muxed_data),
      .out_o(read_buf[i])
    );
  end

  // The buffer enable is allowed to change when the entire read pipeline is idle
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

  logic rsp_order_fifo_wr;
  assign rsp_order_fifo_wr = req_i && rdy_o;

  logic rsp_order_fifo_rd;
  assign rsp_order_fifo_rd = rsp_fifo_vld & data_valid_o;

  flash_phy_rd_buf_dep u_rd_buf_dep (
    .clk_i,
    .rst_ni,
    .en_i(buf_en_q),
    .fifo_wr_i(rsp_order_fifo_wr),
    .fifo_rd_i(rsp_order_fifo_rd),
    .wr_buf_i(rsp_fifo_wdata.buf_sel),
    .rd_buf_i(rsp_fifo_rdata.buf_sel),
    .dependency_o(buf_dependency),
    .all_dependency_o(all_buf_dependency)
  );

  // If width is the same, word_sel is unused
  if (WidthMultiple == 1) begin : gen_single_word_sel
    assign rsp_fifo_wdata.word_sel = '0;
  end else begin : gen_word_sel
    assign rsp_fifo_wdata.word_sel = addr_i[0 +: LsbAddrBit];
  end

  // store the ecc configuration for this transaction until
  // response is ready to be sent.
  assign rsp_fifo_wdata.intg_ecc_en = ecc_i;

  // response order FIFO
  logic rsp_order_fifo_err;
  prim_fifo_sync #(
    .Width  (RspOrderFifoWidth),
    .Pass   (0),
    .Depth  (RspOrderDepth),
    .Secure (1'b1) // SEC_CM: FIFO.CTR.REDUN
  ) u_rsp_order_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(rsp_order_fifo_wr),
    .wready_o(rsp_fifo_rdy),
    .wdata_i (rsp_fifo_wdata),
    .depth_o (),
    .full_o (),
    .rvalid_o(rsp_fifo_vld),
    .rready_i(data_valid_o), // pop when a match has been found
    .rdata_o (rsp_fifo_rdata),
    .err_o   (rsp_order_fifo_err)
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

  // When buffer enable changes, we want to hold off new requests
  // until the request is absorbed.  buf_en_q is allowed to change
  // only when the entire read pipeline is idle, however, during that
  // same cycle there could be a new incoming request.
  //
  // We back pressure here instead of waiting for a period of idle + no
  // request because it potentially means a storm of accesses could
  // prevent the buffer enable from taking effect.
  logic no_buf_en_change;
  assign no_buf_en_change = (buf_en_q == buf_en_i);

  // If no buffers matched, accept only if flash is ready and there is space
  // If buffer is matched, accept as long as there is space in the rsp fifo
  // If all buffers are currently allocated or have a dependency, wait until
  // at least 1 dependency has cleared.
  assign rdy_o = (no_match ? ack_i & flash_rdy & rd_stages_rdy : rd_stages_rdy) &
                 ~all_buf_dependency & no_buf_en_change;

  // issue a transaction to flash only if there is space in read stages,
  // there is no buffer match and flash is not currently busy.
  assign req_o = req_i & no_buf_en_change & flash_rdy & rd_stages_rdy & no_match;

  /////////////////////////////////
  // Handling Reliability ECC
  /////////////////////////////////

  // only uncorrectable errors are passed on to the fabric
  logic data_err;

  // scrambled data must pass through ECC first
  logic valid_ecc;
  logic ecc_multi_err;
  logic ecc_single_err;
  logic [PlainDataWidth-1:0] data_ecc_chk;
  logic [PlainDataWidth-1:0] data_int;
  logic data_erased;

  // this ECC check is for reliability ECC
  assign valid_ecc = rd_done && rd_attrs.ecc;

  // When all bits are 1, the data has been erased
  // This check is only valid when read data returns.
  assign data_erased = rd_done & (data_i == {FullDataWidth{1'b1}});

  prim_secded_hamming_76_68_dec u_dec (
    .data_i(data_i),
    .data_o(data_ecc_chk),
    .syndrome_o(),
    .err_o({ecc_multi_err, ecc_single_err})
  );

  // send out error indication when ecc is enabled
  assign data_err = valid_ecc & ecc_multi_err;

  // reliability ECC errors cause both in-band and out-of-band errors
  assign relbl_ecc_err_o = data_err;

  // If there is a detected multi-bit error or a single bit error, always return the
  // ECC corrected result (even though it is possibly wrong).
  // There is no data error of any kind (specifically when multi_err is disabled), just
  // return the raw data so that it can be debugged.
  assign data_int = data_err | ecc_single_err_o ?
                    data_ecc_chk :
                    data_i[PlainDataWidth-1:0];

  // send out error indication when ecc is enabled
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
  logic [PlainDataWidth-1:0] fifo_data;
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

  logic [1:0] unused_rd_depth, unused_mask_depth;
  logic rd_and_mask_fifo_pop;
  assign rd_and_mask_fifo_pop = fifo_data_ready | fifo_forward_pop;

  logic descram_q, forward_q;
  assign hint_descram = fifo_data_valid & descram_q;
  assign hint_forward = fifo_data_valid & forward_q;

  // See comment above on how FIFO popping can be improved in the future
  logic rd_stage_fifo_err;
  prim_fifo_sync #(
    .Width   (PlainDataWidth + 3 + NumBuf),
    .Pass    (0),
    .Depth   (2),
    .OutputZeroIfEmpty (1),
    .Secure  (1'b1) // SEC_CM: FIFO.CTR.REDUN
  ) u_rd_storage (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(rd_done),
    .wready_o(data_fifo_rdy),
    .wdata_i ({alloc_q, descram, forward, data_err, data_int}),
    .depth_o (unused_rd_depth),
    .full_o (),
    .rvalid_o(fifo_data_valid),
    .rready_i(rd_and_mask_fifo_pop),
    .rdata_o ({alloc_q2, descram_q, forward_q, data_err_q, fifo_data}),
    .err_o   (rd_stage_fifo_err)
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
    .depth_o (unused_mask_depth),
    .full_o (),
    .rvalid_o(mask_valid),
    .rready_i(rd_and_mask_fifo_pop),
    .rdata_o (mask),
    .err_o   ()
  );

  // generate the mask calculation request
  // mask calculation is done in parallel to the read stage
  // calc_req_o is done after req_o is accepted so that most of the
  // cycle can be allocated to mask calculation logic. req_o,
  // unlike calc_req_o, asserts the same cycle the transaction is
  // received, so much of the timing may have already been lost to
  // transaction routing.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      calc_req_o <= '0;
    end else if (req_o && ack_i && descramble_i) begin
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
  assign scrambled_data_o = fifo_data[DataWidth-1:0] ^ mask;

  // muxed responses
  // When "forward" is true, there is nothing ahead in the pipeline, directly feed data
  // and error forward.
  // When "forward" is not true, take the output from the descrmable stage, which is
  // dependent on the scramble hint.
  assign muxed_data = forward      ? data_int :
                      hint_descram ? {fifo_data[PlainDataWidth-1 -: PlainIntgWidth],
                                      descrambled_data_i ^ mask} :
                                     fifo_data;
  assign muxed_err  = forward       ? data_err :
                      ~hint_forward ? data_err_q : '0;

  // muxed data valid
  // if no de-scramble required, return data on read complete
  // if data is all empty (erased), also return data on read complete
  // if descramble is required, return data when descrambler finishes
  // if descramble is not required, but there are transctions ahead, return from fifo when ready
  assign data_valid = forward | ~hint_forward & fifo_data_ready;


  /////////////////////////////////
  // Response
  /////////////////////////////////

  logic flash_rsp_match;
  logic [NumBuf-1:0] buf_rsp_match;
  logic [PlainDataWidth-1:0] buf_rsp_data;
  logic buf_rsp_err;


  // update buffers
  // When forwarding, update entry stored in alloc_q
  // When de-scrambling however, the contents of alloc_q may have already updated to the next read,
  // so a different pointer is used.
  assign update = forward         ? alloc_q  :
                  ~hint_forward & fifo_data_ready ? alloc_q2 : '0;

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
    buf_rsp_err = '0;
    for (int i = 0; i < NumBuf; i++) begin
      if (buf_rsp_match[i]) begin
        buf_rsp_data = read_buf[i].data;
        buf_rsp_err = buf_rsp_err | read_buf[i].err;
      end
    end
  end

  logic [PlainDataWidth-1:0] data_out_muxed;
  assign data_out_muxed = |buf_rsp_match ? buf_rsp_data : muxed_data;

  logic [BusWidth-1:0] data_out_pre;
  if (WidthMultiple == 1) begin : gen_width_one_rd
    // When multiple is 1, just pass the read through directly
    logic unused_word_sel;
    assign data_out_pre = data_err_o ? {BusWidth{1'b1}} : data_out_muxed[DataWidth-1:0];
    assign unused_word_sel = rsp_fifo_rdata.word_sel;

  end else begin : gen_rd
    // Re-arrange data into packed array to pick the correct one
    logic [WidthMultiple-1:0][BusWidth-1:0] bus_words_packed;
    assign bus_words_packed = data_out_muxed[DataWidth-1:0];
    assign data_out_pre = data_err_o ? {BusWidth{1'b1}} : bus_words_packed[rsp_fifo_rdata.word_sel];
  end

  // use the tlul integrity module directly for bus integrity
  // SEC_CM: MEM.BUS.INTEGRITY
  tlul_data_integ_enc u_bus_intg (
    .data_i(data_out_pre),
    .data_intg_o(data_o)
  );

  // add plaintext decoding here
  // plaintext error
  logic intg_err_pre, intg_err;
  logic [DataWidth-1:0] unused_data;
  logic [3:0] unused_intg;
  logic [3:0] truncated_intg;

  prim_secded_hamming_72_64_enc u_plain_enc (
    .data_i(data_out_muxed[DataWidth-1:0]),
    .data_o({unused_intg, truncated_intg, unused_data})
  );
  assign intg_err_pre = rsp_fifo_rdata.intg_ecc_en ?
                        truncated_intg != data_out_muxed[DataWidth +: PlainIntgWidth] :
                        '0;

  prim_sec_anchor_buf #(
    .Width(1)
  ) u_intg_buf (
    .in_i(intg_err_pre),
    .out_o(intg_err)
  );

  // whenever the response is coming from the buffer, the error is never set
  assign data_valid_o = flash_rsp_match | (|buf_rsp_match);

  // integrity and reliability ECC errors always cause in band errors
  assign data_err_o   = data_valid_o & (muxed_err | intg_err | (|buf_rsp_match & buf_rsp_err)) |
                        arb_err_i;

  // integrity ECC error can also cause out of band alert
  assign intg_ecc_err_o = data_valid_o & intg_err;

  // the entire read pipeline is idle when there are no responses to return and no
  assign idle_o = ~rsp_fifo_vld;

  // if any fifo shows an integrity error
  assign fifo_err_o = |{rsp_order_fifo_err, rd_stage_fifo_err};

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

  // buffer response match should happen only to 1 buffer at time
  `ASSERT(OneHotRspMatch_A, $onehot0(buf_rsp_match))

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

  // The read storage depth and mask depth should always be the same after popping
  //`ASSERT(FifoSameDepth_A, rd_and_mask_fifo_pop |=> unused_rd_depth == unused_mask_depth)

  /////////////////////////////////
  // Functional coverage points to add
  /////////////////////////////////

  // exercise both flash_read and de-scramble stages at the same time
  // - make sure accesses can be consecutive or random
  // exercise back to back transactions, and transactions with varying delays
  // exercise data hazard where erase / program requires buffer eviction

endmodule // flash_phy_core
