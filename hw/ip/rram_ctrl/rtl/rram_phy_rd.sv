// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM phy read module. rram_phy_rd consists of a three stage pipeline:
// stage 1: read-buffer lookup, RRAM request
// stage 2: descrambling
// stage 3: update read-buffer, return data
//
// If a requested word is not in the read-buffer, the data will be requested from the RRAM.
// At the same time, a read-buffer is allocated with the request address and partition.
// If the requested word is already in the read-buffer, it can be returned in the next cycle.
//

module rram_phy_rd
  import rram_ctrl_pkg::*;
(
  input  logic                    clk_i,
  input  logic                    rst_ni,
  // RRAM phy interface
  input  logic                    req_i,
  output logic                    ack_o,
  input  logic                    ecc_en_i,
  input  logic                    descramble_en_i,
  input  logic                    wr_req_i,
  input  logic [PageW-1:0]        wr_page_addr_i,
  input  rram_part_e              wr_part_i,
  input  logic [BusAddrW-1:0]     addr_i,
  input  rram_part_e              part_i,
  output logic                    data_valid_o,
  output logic                    data_err_o,
  output logic [BusFullWidth-1:0] data_o,
  // scrambling module connections
  output scramble_req_t           scramble_req_o,
  input  scramble_rsp_t           scramble_rsp_i,
  // RRAM macro connections
  output logic                    rd_req_o,
  input  logic                    rd_ack_i,  // ack means a request has been accepted by RRAM
  input  logic                    rd_done_i, // done means a request has been completed
  output logic [AddrW-1:0]        rd_addr_o,
  output rram_part_e              rd_part_o,
  output logic                    rd_ecc_en_o,
  input  logic [DataWidth-1:0]    rd_rdata_i,
  input  logic                    rd_ecc_err_i,
  input  logic                    rd_err_i,
  // status signals
  output logic                    idle_o,
  // error signals
  output logic                    intg_err_o,
  output logic                    ctrl_err_o,
  output logic                    ecc_fatal_err_o,
  output logic                    fifo_err_o
);

  logic [WidthMultiple-1:0][BusFullWidth-1:0] muxed_data;
  logic                                       muxed_err;
  logic [WidthMultiple-1:0][BusFullWidth-1:0] rram_data_packed_intg;

  /////////////////////////////////
  // Error signals
  /////////////////////////////////
  logic valid_err, req_err, cmd_intg_err;

  /////////////////////////////////
  // Descrambling signals
  /////////////////////////////////
  logic calc_start, calc_done, calc_busy_q;

  /////////////////////////////////
  // RRAM read signals
  /////////////////////////////////
  logic rd_busy, rd_rdy;

  /////////////////////////////////
  // Meta fifo signals
  /////////////////////////////////
  meta_entry_t meta_d, meta_q;
  logic meta_fifo_req, meta_fifo_rdy, meta_fifo_valid, meta_fifo_pop;
  logic meta_fifo_err;
  logic [prim_util_pkg::vbits(NumOutstandingRdReq + 1)-1:0] unused_meta_depth;

  /////////////////////////////////
  // Rd-fifo signals
  /////////////////////////////////
  rd_rsp_entry_t rd_fifo_d, rd_fifo_q;
  logic          rd_fifo_req, rd_fifo_rdy, rd_fifo_valid, rd_fifo_pop;
  logic          rd_fifo_err;
  logic [1:0]    unused_rd_depth;

  /////////////////////////////////
  // Mask fifo signals
  /////////////////////////////////
  logic                 mask_fifo_req, mask_fifo_rdy, mask_fifo_valid, mask_fifo_pop;
  logic                 mask_fifo_err;
  logic [1:0]           unused_mask_depth;
  logic [DataWidth-1:0] mask_q;

  logic all_fifo_valid;
  logic all_fifo_rdy;

  /////////////////////////////////
  // Read buffer signals
  /////////////////////////////////

  // A buffer allocate is invoked when a new transaction arrives.
  // Alloc only happens if the new transaction does not match an existing entry.
  logic [NumRdBuf-1:0] alloc;

  // A buffer update is invoked after the completion of the de-scramble stage.
  // This updates the buffer that was allocated when a new transaction was initiated.
  logic [NumRdBuf-1:0] update;
  logic [NumRdBuf-1:0] verify;

  rd_buf_t rd_buf [NumRdBuf];
  logic    rd_buf_descramble_en;
  logic    rd_buf_ecc_en;
  logic    rd_buf_miss;
  logic    rd_buf_hit;
  logic    rd_buf_update;

  logic [NumRdBuf-1:0] buf_invalid;
  logic [NumRdBuf-1:0] buf_wip;
  logic [NumRdBuf-1:0] buf_valid;
  logic [NumRdBuf-1:0] buf_verified;
  logic [NumRdBuf-1:0] buf_intg_err;
  logic [NumRdBuf-1:0] buf_dependency;
  logic [NumRdBuf-1:0] buf_invalid_alloc;
  logic [NumRdBuf-1:0] buf_verified_alloc;
  logic [NumRdBuf-1:0] buf_alloc;
  logic [NumRdBuf-1:0] buf_to_verify;
  logic [NumRdBuf-1:0] buf_to_verify_masked;

  // The new transaction matches an already allocated buffer.
  // The buffer may be valid or work in progress.
  logic [NumRdBuf-1:0] buf_match;
  logic                no_match;

  // There is a stateful operation aimed at valid buffer, that buffer must be flushed
  logic [NumRdBuf-1:0] buf_invalidate;

  // RRAM word address
  logic [AddrW-1:0] rram_word_addr;

  // Shadow request signals
  logic             shadow_rd_req, rd_req;
  logic             shadow_rd_gnt, rd_gnt;
  logic             shadow_sel;
  logic [AddrW-1:0] shadow_rram_word_addr;
  rram_part_e       shadow_rram_part;
  logic             shadow_descramble_en;
  logic             shadow_ecc_en;

  /////////////////////////////////
  // Read-buffers
  /////////////////////////////////
  // The next allocated buffer is determined in the following way:
  // - If there is an invalid buffer, use that lowest one
  // - If there are no invalid buffers, pick a verified buffer
  // - If no invalid or verified buffer exist, stall the request until a buffer is verified

  assign rram_word_addr = addr_i[BusAddrW-1 -: AddrW];

  for (genvar i = 0; i < NumRdBuf; i++) begin: gen_buf_states
    assign buf_valid[i]    = rd_buf[i].attr == Valid;
    assign buf_verified[i] = rd_buf[i].attr == Verified;
    assign buf_wip[i]      = rd_buf[i].attr == Alloc;

    // If a buffer contains an error, it is considered invalid
    assign buf_invalid[i] = (rd_buf[i].attr == Invalid) | rd_buf[i].err;
  end

  assign buf_invalid_alloc[0] = buf_invalid[0];
  for (genvar i = 1; i < NumRdBuf; i++) begin: gen_inv_alloc_bufs
    assign buf_invalid_alloc[i] = buf_invalid[i] & ~|buf_invalid[i-1:0];
  end

  // A prim arbiter is used to select among the valid buffers
  logic [1:0] dummy_data [NumRdBuf];
  assign dummy_data = '{default: '0};

  prim_arbiter_tree #(
    .N(NumRdBuf),
    .DW(2),
    .EnDataPort(1'b0)
  ) u_buf_sel_random (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b0),
    // If all buffers have a dependency to an in-flight transaction, do not
    // allocate and wait for the dependencies to end.
    .req_i(buf_verified & ~buf_dependency),
    .data_i(dummy_data),
    .gnt_o(buf_verified_alloc),
    .idx_o(),
    .valid_o(),
    .data_o(),
    .ready_i(1'b1)
  );

  // Select buffer to replace: invalid or verified
  assign buf_alloc = |buf_invalid_alloc ? buf_invalid_alloc : buf_verified_alloc;

  // Check if:
  // - requested data is in any read-buffer
  // - any of the read-buffers must be invalidated
  for (genvar i = 0; i < NumRdBuf; i++) begin: gen_buf_match
    logic part_match;
    logic descramble_match;

    assign part_match = rd_buf[i].part == part_i;

    assign descramble_match = rd_buf[i].descramble_en == descramble_en_i;

    assign buf_match[i] = req_i &
                          (buf_wip[i] | buf_valid[i] | buf_verified[i]) &
                          (rd_buf[i].addr == rram_word_addr) &
                          ~rd_buf[i].err &
                          part_match &
                          descramble_match;

    // The content of the rd_buffer must be cleared if a write operation to the same page and
    // partition has been observed
    logic page_addr_match;

    assign page_addr_match = (rd_buf[i].addr[AddrW-1 -: PageW] == wr_page_addr_i) &
                             (rd_buf[i].part == wr_part_i);
    assign buf_invalidate[i] = wr_req_i & page_addr_match;
  end

  assign no_match = ~|buf_match;

  // in case of a rd-buffer miss, allocate a new entry in read buffer
  assign alloc = no_match & ack_o ? buf_alloc : '0;

  // Read-buffers:
  // "allocate" clears data and allocates the buffer to the current address
  // "update" writes the content to the read buffer
  // "invalidate" clears the buffer and sets it to invalid
  // "verify" checks if the data matches the existing entry and sets the buffer to verified
  for (genvar i = 0; i < NumRdBuf; i++) begin: gen_bufs
    rram_phy_rd_buffer u_rram_phy_rd_buffer (
      .clk_i,
      .rst_ni,
      .alloc_i        (alloc[i] & req_i & ack_o),
      .update_i       (update[i]),
      .invalidate_i   (buf_invalidate[i]),
      .verify_i       (verify[i]),
      .addr_i         (rram_word_addr),
      .part_i         (part_i),
      .descramble_en_i(descramble_en_i),
      .ecc_en_i       (ecc_en_i),
      .data_i         (rram_data_packed_intg),
      .err_i          (rd_fifo_q.err),
      .rd_buf_o       (rd_buf[i]),
      .intg_err_o     (buf_intg_err[i])
    );
  end

  // In case of shadow request (shadow_sel) we cannot ack any requests
  // In case of a rd-buf miss we can only accept new requests if
  // - the RRAM has acknowledged the outgoing request (rd_ack_i)
  // - no other rram_rd_req is pending (rd_rdy)
  // - the fifos have space (*fifo_rdy)
  // - there is an allocatable buffer (verified and without dependency or invalid) (|buf_alloc)
  // In case of a rd-buf hit we can accept new requests as long as there is:
  // - space in the meta fifo
  assign ack_o = req_i & ~shadow_sel & (no_match ? rd_ack_i & rd_rdy & all_fifo_rdy & (|buf_alloc) :
                                                   meta_fifo_rdy);

  /////////////////////////
  // Read-buf dependency //
  /////////////////////////
  rram_phy_rd_buf_dep #(
    .Depth(NumOutstandingRdReq)
  ) u_rram_phy_rd_buf_dep (
    .clk_i,
    .rst_ni,
    .fifo_wr_i   (meta_fifo_req & meta_fifo_rdy),
    .fifo_rd_i   (meta_fifo_pop & meta_fifo_valid),
    .wr_buf_i    (meta_d.buf_sel),
    .rd_buf_i    (meta_q.buf_sel),
    .dependency_o(buf_dependency)
  );

  //////////////////////////
  // RRAM shadow requests //
  //////////////////////////

  // Select from all valid buffers one to verify
  prim_arbiter_tree #(
    .N(NumRdBuf),
    .DW(2),
    .EnDataPort(1'b0)
  ) u_buf_sel_verify (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b0),
    .req_i    (buf_valid),
    .data_i   (dummy_data),
    .gnt_o    (buf_to_verify),
    .idx_o    (),
    .valid_o  (),
    .data_o   (),
    .ready_i  (1'b1)
  );

  // Mask out current request if a verification of its content is already ongoing
  assign buf_to_verify_masked = buf_to_verify &
                                ~({NumRdBuf{meta_q.verify & meta_fifo_valid}} &
                                meta_q.buf_sel);

  // Collect address, partition, scrambling and ECC information for the selected buffer
  always_comb begin
    shadow_rram_word_addr = '0;
    shadow_rram_part      = RramPartData;
    shadow_descramble_en  = 1'b0;
    shadow_ecc_en         = 1'b1;
    for (int i = 0; i < NumRdBuf; i++) begin
      if (buf_to_verify_masked[i]) begin
        shadow_rram_word_addr = rd_buf[i].addr;
        shadow_rram_part      = rd_buf[i].part;
        shadow_descramble_en  = rd_buf[i].descramble_en;
        shadow_ecc_en         = rd_buf[i].ecc_en;
      end
    end
  end

  // Issue shadow request if
  // - meta_fifo_rdy (meta fifo is not full)
  // - rd_rdy (no other rram request is pending)
  // - req_i & no_match (no normal request)
  // - buf_to_verify_masked (there is at least one entry in the rd-buffer that needs to be verified)
  // - previous mask calc request has not finished
  assign shadow_rd_req = meta_fifo_rdy & rd_rdy & (~req_i | no_match) & |buf_to_verify_masked &
                         !(shadow_descramble_en && calc_busy_q);
  // Issue normal request if
  // - meta_fifo_rdy (meta fifo is not full)
  // - rd_rdy (no other rram request is pending)
  // - req_i & no_match (rd buffer miss)
  // - buf_alloc != '0 (there is space in the read buffer to allocate the data)
  // - previous mask calc request has not finished
  assign rd_req = meta_fifo_rdy & rd_rdy & req_i & no_match & (buf_alloc != '0) &
                  !(descramble_en_i && calc_busy_q);

  /////////////////
  // RRAM Access //
  /////////////////
  prim_arbiter_tree #(
    .N(2),
    .DW(1),
    .EnDataPort(1'b0)
  ) u_req_sel (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b0),
    .req_i    ({shadow_rd_req, rd_req}),
    .data_i   ('{default: '0}),
    .gnt_o    ({shadow_rd_gnt, rd_gnt}),
    .idx_o    (),
    .valid_o  (rd_req_o),
    .data_o   (),
    .ready_i  (1'b1)
  );
  assign shadow_sel = shadow_rd_req & shadow_rd_gnt & ~rd_gnt;

  assign rd_addr_o   = shadow_sel ? shadow_rram_word_addr : rram_word_addr;
  assign rd_part_o   = shadow_sel ? shadow_rram_part      : part_i;
  assign rd_ecc_en_o = shadow_sel ? shadow_ecc_en         : ecc_en_i;

  // only use when there are outstanding read transactions
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_busy <= '0;
    end else if (rd_req_o & rd_ack_i) begin
      rd_busy <= 1'b1;
    end else if (rd_busy & rd_done_i) begin
      rd_busy <= 1'b0;
    end
  end

  // we can only issue one read_request at the time
  assign rd_rdy = ~rd_busy | (rd_busy & rd_done_i);

  ////////////////////////////////
  // storage for rram read data //
  ////////////////////////////////
  assign rd_fifo_req = rd_busy & rd_done_i;

  // storage for read data from RRAM
  assign rd_fifo_d.err  = rd_ecc_err_i | rd_err_i;
  assign rd_fifo_d.data = rd_rdata_i;

  prim_fifo_sync #(
    .Width             (RdRspFifoWidth),
    .Pass              (0),
    .Depth             (2),
    .OutputZeroIfEmpty (1),
    .NeverClears       (1'b1),
    .Secure            (1'b1) // SEC_CM: FIFO.CTR.REDUN
  ) u_rd_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(rd_fifo_req),
    .wready_o(rd_fifo_rdy),
    .wdata_i (rd_fifo_d),
    .depth_o (unused_rd_depth),
    .full_o  (),
    .rvalid_o(rd_fifo_valid),
    .rready_i(rd_fifo_pop),
    .rdata_o (rd_fifo_q),
    .err_o   (rd_fifo_err)
  );

  ///////////////////////////////////////////
  // storage for mask from scrambling unit //
  ///////////////////////////////////////////
  assign mask_fifo_req = calc_done;

  prim_fifo_sync #(
    .Width             (DataWidth),
    .Pass              (0),
    .Depth             (2),
    .NeverClears       (1'b1),
    .OutputZeroIfEmpty (1),
    .Secure            (1'b1) // SEC_CM: FIFO.CTR.REDUN
  ) u_mask_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(mask_fifo_req),
    .wready_o(mask_fifo_rdy),
    .wdata_i (scramble_rsp_i.mask),
    .depth_o (unused_mask_depth),
    .full_o  (),
    .rvalid_o(mask_fifo_valid),
    .rready_i(mask_fifo_pop),
    .rdata_o (mask_q),
    .err_o   (mask_fifo_err)
  );

  ///////////////////////////////////////////////////////////////////
  // Storage for read meta data that is used later in the pipeline //
  ///////////////////////////////////////////////////////////////////
  assign meta_d.buf_sel  = shadow_sel ? buf_to_verify_masked : (|alloc ? alloc : buf_match);
  assign meta_d.update   = shadow_sel ? 1'b0 : |alloc;
  assign meta_d.verify   = shadow_sel;
  assign meta_d.word_sel = shadow_sel ? '0 : addr_i[WordSelW-1:0];

  // Command integrity of incoming requests (stored in meta fifo and checked with response)
  logic [21:0] unused_cmd_data0;
  prim_secded_inv_28_22_enc u_cmd_intg_req_gen (
    .data_i({ecc_en_i, descramble_en_i, addr_i, part_i}),
    .data_o({meta_d.cmd_intg, unused_cmd_data0})
  );

  assign meta_fifo_req = meta_fifo_rdy & (req_i & ~no_match & ack_o | (rd_req_o & rd_ack_i));

  prim_fifo_sync #(
    .Width             (MetaFifoWidth),
    .Pass              (0),
    .Depth             (NumOutstandingRdReq),
    .NeverClears       (1'b1),
    .OutputZeroIfEmpty (1),
    .Secure            (1'b1) // SEC_CM: FIFO.CTR.REDUN
  ) u_meta_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(meta_fifo_req),
    .wready_o(meta_fifo_rdy),
    .wdata_i (meta_d),
    .depth_o (unused_meta_depth),
    .full_o  (),
    .rvalid_o(meta_fifo_valid),
    .rready_i(meta_fifo_pop),
    .rdata_o (meta_q),
    .err_o   (meta_fifo_err)
  );

  assign all_fifo_valid = rd_fifo_valid & mask_fifo_valid & meta_fifo_valid;
  assign all_fifo_rdy   = rd_fifo_rdy & mask_fifo_rdy & meta_fifo_rdy;

  ///////////////////////
  // RRAM descrambling //
  ///////////////////////
  logic             rd_data_valid;
  logic [AddrW-1:0] calc_addr_q, calc_addr_d;

  assign calc_addr_d = shadow_sel ? shadow_rram_word_addr : rram_word_addr;
  // Mask computation can be started while RRAM is accessed
  assign calc_start = ((shadow_sel ? shadow_descramble_en : descramble_en_i) ?
                      rd_req_o & rd_ack_i :
                      1'b0);
  assign calc_done = calc_busy_q & scramble_rsp_i.calc_ack;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      calc_busy_q <= '0;
      calc_addr_q <= '0;
    end else if (calc_start) begin
      calc_busy_q <= 1'b1;
      calc_addr_q <= calc_addr_d;
    end else if (calc_done) begin
      calc_busy_q <= 1'b0;
      calc_addr_q <= '0;
    end
  end
  if (MaskReqReg) begin : gen_registered_mask_req
    `ASSERT(PendingCalcReq, (calc_start |-> ((calc_busy_q == 1'b0) || (calc_done == 1'b1))))
    assign scramble_req_o.calc_req = calc_busy_q;
    assign scramble_req_o.addr     = calc_addr_q;
  end else begin : gen_direct_mask_req
    `ASSERT(PendingCalcReq, (calc_start |-> (calc_busy_q == 1'b0)))
    assign scramble_req_o.calc_req = calc_start ? 1'b1        : calc_busy_q;
    assign scramble_req_o.addr     = calc_start ? calc_addr_d : calc_addr_q;
  end

  // Descrambling request can be started if mask and storage fifos are ready.
  assign rd_buf_update = meta_fifo_valid & meta_q.update;
  assign rd_buf_miss   = meta_fifo_valid & (meta_q.update | meta_q.verify);
  assign rd_buf_hit    = meta_fifo_valid & !(meta_q.update | meta_q.verify);

  assign scramble_req_o.op_req        = all_fifo_valid & rd_buf_descramble_en;
  assign scramble_req_o.data_in       = rd_fifo_q.data ^ mask_q;
  assign scramble_req_o.cipher_switch = meta_q.verify & rd_buf_descramble_en;
  assign scramble_req_o.op_type       = DeScrambleOp;

  assign meta_fifo_pop = meta_fifo_valid & ((rd_data_valid & rd_buf_miss) | rd_buf_hit);
  assign rd_fifo_pop   = rd_data_valid & rd_buf_miss;
  assign mask_fifo_pop = mask_fifo_valid & rd_data_valid & rd_buf_miss & rd_buf_descramble_en;

  assign rd_data_valid = rd_buf_descramble_en ? scramble_rsp_i.op_ack & all_fifo_valid :
                                                meta_fifo_valid & rd_fifo_valid;

  ////////////////////////////
  // Phy rd output response //
  ////////////////////////////
  logic [DataWidth-1:0]                       rram_data;
  logic [AddrW-1:0]                           rd_buf_addr;
  rram_part_e                                 rd_buf_part;
  logic [WidthMultiple-1:0][BusFullWidth-1:0] rd_buf_data;
  logic                                       rd_buf_err;

  logic [WidthMultiple-1:0][BusWidth-1:0]              rram_data_packed;
  logic [WidthMultiple-1:0][BusWidth-1:0]              rram_data_packed_xor;
  logic [WidthMultiple-1:0][BusWidth-1:0]              rram_addr_packed;
  logic [WidthMultiple-1:0][BusFullWidth-BusWidth-1:0] rram_packed_intg;

  assign rram_data = rd_buf_descramble_en ? scramble_rsp_i.data_out ^ mask_q : rd_fifo_q.data;

  for (genvar i = 0; i < WidthMultiple; i++) begin : gen_bus_words_intg
    logic [BusWidth-1:0] unused_data;
    logic [WordSelW-1:0] offset;
    // 1. convert RRAM word to packed bus words
    // 2. remove addr-xor
    // 3. compute integrity per bus word (without addr-xor)
    // 4. combine integrity with address-infected data (xor on data will be removed in controller)
    assign offset = WordSelW'(unsigned'(i));

    assign rram_data_packed[i]     = rram_data[i*BusWidth +: BusWidth];
    assign rram_addr_packed[i]     = {{(BusWidth-BusAddrW){1'b0}}, rd_buf_addr, offset};
    assign rram_data_packed_xor[i] = rram_data_packed[i] ^ rram_addr_packed[i];
    // SEC_CM: MEM.BUS.INTEGRITY
    tlul_data_integ_enc u_rram_bus_intg (
      .data_i     (rram_data_packed_xor[i]),
      .data_intg_o({rram_packed_intg[i], unused_data})
    );
    assign rram_data_packed_intg[i] = {rram_packed_intg[i], rram_data_packed[i]};
  end

  // Select from rd-buf if content is valid
  always_comb begin
    rd_buf_addr          = '0;
    rd_buf_part          = RramPartData;
    rd_buf_descramble_en = 1'b0;
    rd_buf_ecc_en        = 1'b1;
    rd_buf_data          = '0;
    rd_buf_err           = '0;
    for (int i = 0; i < NumRdBuf; i++) begin
      if (meta_q.buf_sel[i]) begin
        // Data, err is only valid if entry is valid or verified
        if (rd_buf_hit & (buf_valid[i] | buf_verified[i])) begin
          rd_buf_data = rd_buf[i].data;
          rd_buf_err  = rd_buf[i].err;
        end
        // Addr, part, descramble ecc_en if entry is alloc, valid or verified (not invalid)
        if (~buf_invalid[i]) begin
          rd_buf_addr          = rd_buf[i].addr;
          rd_buf_part          = rd_buf[i].part;
          rd_buf_descramble_en = rd_buf[i].descramble_en;
          rd_buf_ecc_en        = rd_buf[i].ecc_en;
        end
      end
    end
  end

  // Select rram content either from descrambling/rd-fifo or from rd-buf
  assign muxed_data = rd_buf_update ? rram_data_packed_intg : rd_buf_data;
  assign muxed_err  = rd_buf_update ? rd_fifo_q.err : rd_buf_err;

  // If update or verify is set, write data back to rd-buf
  assign update = meta_q.buf_sel & {NumRdBuf{rd_data_valid & rd_buf_update}};
  assign verify = meta_q.buf_sel & {NumRdBuf{rd_data_valid & meta_q.verify}};

  ///////////////////////////////
  // Output response selection //
  ///////////////////////////////
  logic [BusFullWidth-1:0] inv_data;
  tlul_data_integ_enc u_bus_intg (
    .data_i     ({BusWidth{1'b1}}),
    .data_intg_o(inv_data)
  );

  // Output is valid whenever we have:
  // - a rd_buf hit
  // - a rd_buf_update as it is forwarded to the output
  assign data_valid_o = (rd_data_valid & rd_buf_update) | rd_buf_hit;
  // Select right bus word and return
  assign data_o     = (data_valid_o & ~data_err_o) ? muxed_data[meta_q.word_sel] : inv_data;
  assign data_err_o = data_valid_o ? muxed_err | cmd_intg_err : 1'b0;

  // The read module is idle when there are no outstanding transactions to process
  // (the meta fifo is empty) and no new requests enter the pipeline or no new shadow requests are
  // generated. This indicator is used by the phy_wr module.
  assign idle_o = ~meta_fifo_valid & ~req_i & ~shadow_rd_req;

  /////////////////////////
  // Errors caused by FI //
  /////////////////////////
  // Check command integrity, illegal combination of signals and the integrity of FIFOs

  // Prim buffers to prevent optimization of error condition signals
  meta_entry_t meta_q_buf;
  prim_buf #(
    .Width($bits(meta_q))
  ) u_prim_buf_meta (
    .in_i (meta_q),
    .out_o(meta_q_buf)
  );
  // some fields of meta_q_buf are not used for the check.
  logic unused_meta_q_buf;
  assign unused_meta_q_buf = (^meta_q_buf.update) ^ (^meta_q_buf.buf_sel);

  // valid cannot be one if:
  // - meta_fifo is empty
  // - the current operation is a verify operation
  // - the meta_fifo is not popped
  assign valid_err = data_valid_o & (~meta_fifo_valid | meta_q_buf.verify | ~meta_fifo_pop);

  // There cannot be a rram_rd_req if:
  // - there is no incoming request
  // - there is no shadow request
  assign req_err = rd_req_o & (~(req_i | shadow_rd_req));

  // Command integrity must match for all valid data responses
  logic [21:0] unused_cmd_data1;
  logic [5:0]  cmd_rsp_intg;

  // Command integrity of response
  prim_secded_inv_28_22_enc u_cmd_intg_rsp_gen (
    .data_i({rd_buf_ecc_en, rd_buf_descramble_en, rd_buf_addr, meta_q_buf.word_sel, rd_buf_part}),
    .data_o({cmd_rsp_intg, unused_cmd_data1})
  );

  assign cmd_intg_err = data_valid_o ? (cmd_rsp_intg != meta_q_buf.cmd_intg) : 1'b0;

  // Control flow error if any of the above errors is set
  assign ctrl_err_o = valid_err | req_err | cmd_intg_err;

  // If any fifo shows an integrity error
  assign fifo_err_o = |{meta_fifo_err, rd_fifo_err, mask_fifo_err};

  // Integrity error if a verify operation found a mismatch
  assign intg_err_o = |buf_intg_err;

  // If an uncorrectable error is detected
  assign ecc_fatal_err_o = rd_fifo_req & rd_ecc_err_i;

  ////////////////
  // Assertions //
  ////////////////

  // Abort when an integrity error is seen
  `ASSERT(IntgError, (buf_intg_err == '0))

endmodule // rram_phy_rd
