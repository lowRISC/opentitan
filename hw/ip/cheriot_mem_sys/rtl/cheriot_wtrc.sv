// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Write-to-read-and-compare (WTRC) filter for capability stores to the read-only NVM, on the host
// port of the tag filter. The NVM cannot be written, so such a store is turned into a read of the
// word it targets, and succeeds if the NVM already holds its data and data integrity.
module cheriot_wtrc #(
  // The number of requests the tag filter takes before it answers the first
  parameter int unsigned NumOutstanding = 32'd2,
  // TL-UL address type
  parameter type   addr_t               = logic [top_pkg::TL_AW-1:0],
  // The NVM, and the base address of its tag region in the meta SRAM
  parameter addr_t NvmBaseAddr          = 'h3000_0000,
  parameter addr_t MetaNvmTagBase       = 'h1100_0C00
)(
  input  logic clk_i,
  input  logic rst_ni,

  // Device port
  input  tlul_pkg::tl_h2d_t tl_d_i,
  input  logic              cap_store_i,
  input  logic              req_done_i,
  output tlul_pkg::tl_d2h_t tl_d_o,

  // Host port, towards the NVM
  output tlul_pkg::tl_h2d_t tl_h_o,
  input  tlul_pkg::tl_d2h_t tl_h_i,

  // Meta port
  output tlul_pkg::tl_h2d_t tl_m_o,
  output logic [4:0]        bit_sel_m_o,
  input  logic              m_ready_i,

  // The oldest unanswered request is a W1 whose tag write has been issued
  output logic tag_wr_o,

  // Fatal error
  output logic err_o
);

  ///////////
  // Types //
  ///////////

  localparam int unsigned AddrWidth = $bits(addr_t);

  // Size of a full-word access
  localparam int unsigned                WordSizeInt = $clog2(top_pkg::TL_DBW);
  localparam logic [top_pkg::TL_SZW-1:0] WordSize    = top_pkg::TL_SZW'(WordSizeInt);

  // The address of a capability: that of its W0, without the word and byte offset
  typedef logic [AddrWidth-1:3] cap_addr_t;

  // Where the capability being stored is in its sequence
  typedef enum logic [1:0] {
    CapIdle,  // no capability open
    CapW0,    // W0 taken, waiting for its W1
    CapW1,    // W1 taken, neither answered nor turned into a tag write yet
    CapTagWr  // W1's tag write issued, waiting for its answer
  } cap_state_e;

  // The fields of an NVM offset that locate its capability tag
  typedef struct packed {
    logic [AddrWidth-1:8] meta_word;
    logic [7:3]           bit_sel;
    logic [2:0]           rsvd;
  } meta_addr_t;

  // What the response of a request is checked against, handed from the request to the response
  // channel
  typedef struct packed {
    logic                               cap_store;
    logic                               upper;
    logic                               bad;
    logic [top_pkg::TL_DW-1:0]          data;
    logic [tlul_pkg::DataIntgWidth-1:0] data_intg;
  } exp_t;


  /////////////
  // Signals //
  /////////////

  // The request is a capability store of W0 or W1, and not a full-word one
  logic is_w0;
  logic is_w1;
  logic partial_write;

  // A W0 or a W1 is taken
  logic take_w0;
  logic take_w1;

  // The request breaks the W0-then-W1 sequence
  logic seq_violation;

  // Command integrity error of the request
  logic cmd_intg_err;

  // Input and output port of the expect FIFO
  exp_t exp_req;
  logic exp_req_ready;
  exp_t exp_rsp;
  logic exp_rsp_valid;

  // The response at the head of the expect FIFO answers W0 or W1
  logic head_w0;
  logic head_w1;
  logic head_cap;

  // The word read is not the one to be stored
  logic mismatch;

  // The NVM response of a verified W1 becomes its tag write
  logic tag_wr_req;
  logic tag_wr_done;

  // Response integrity error of the NVM response to a capability store
  logic rsp_intg_err;

  // A response is taken, and whether it is the answer of the open W1
  logic rsp_done;
  logic w1_done;

  // The capability being stored
  cap_state_e cap_state_d, cap_state_q;
  cap_addr_t  cap_q;
  logic       w0_ok_q;
  cap_addr_t  req_cap;

  // W1's tag write has been issued, and its answer is pending
  logic tag_wr;

  // A request is presented between W1 and its tag write or answer
  logic req_before_tag_wr;

  // A request out of sequence is taken, or presented before W1's tag write
  logic seq_err;

  // Size and source of W1, for the acknowledgement after its tag write
  logic [top_pkg::TL_SZW-1:0] tag_wr_size_q;
  logic [top_pkg::TL_AIW-1:0] tag_wr_source_q;

  // Where the tag of the capability is
  meta_addr_t tag_stem;

  // Response built here, before and after its integrity is generated
  tlul_pkg::tl_d2h_t own_rsp;
  tlul_pkg::tl_d2h_t own_rsp_intg;


  /////////////
  // Request //
  /////////////

  assign is_w0         = cap_store_i && !tl_d_i.a_address[2];
  assign is_w1         = cap_store_i &&  tl_d_i.a_address[2];
  assign partial_write = !(tl_d_i.a_opcode == tlul_pkg::PutFullData &&
                           tl_d_i.a_mask   == '1                    &&
                           tl_d_i.a_size   == WordSize);

  assign exp_req = '{
    cap_store: cap_store_i,
    upper:     tl_d_i.a_address[2],
    bad:       partial_write || seq_violation,
    data:      tl_d_i.a_data,
    data_intg: tl_d_i.a_user.data_intg
  };

  // The command integrity is recomputed for a capability store, so it is checked first.
  tlul_cmd_intg_chk u_tlul_cmd_intg_chk (
    .tl_i (tl_d_i),
    .err_o(cmd_intg_err)
  );

  // A capability store becomes a read of the same word. Its data and data integrity are kept.
  always_comb begin : proc_connect_tl_req
    tl_h_o         = tl_d_i;
    tl_h_o.d_ready = !tag_wr && (tag_wr_req ? m_ready_i : tl_d_i.d_ready);
    if (cap_store_i) begin
      tl_h_o.a_opcode        = tlul_pkg::Get;
      tl_h_o.a_user.cmd_intg = tlul_pkg::get_cmd_intg(tl_h_o);
    end
  end


  /////////////////
  // Expect FIFO //
  /////////////////

  // Written when the tag filter takes the request, alongside its meta FIFO.
  prim_fifo_sync #(
    .Width($bits(exp_t)),
    .Pass(1'b0),
    .Depth(NumOutstanding)
  ) u_prim_fifo_sync_exp (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(req_done_i),
    .wready_o(exp_req_ready),
    .wdata_i (exp_req),
    .rvalid_o(exp_rsp_valid),
    .rready_i(tl_h_i.d_valid && tl_h_o.d_ready),
    .rdata_o (exp_rsp),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );


  //////////////
  // Response //
  //////////////

  assign head_cap = exp_rsp_valid && exp_rsp.cap_store && !tag_wr;
  assign head_w0  = head_cap && !exp_rsp.upper;
  assign head_w1  = head_cap &&  exp_rsp.upper;

  // The word read must be exactly the one to be stored, data and integrity: comparing only the
  // integrity misses data differences with the same code.
  assign mismatch = tl_h_i.d_error || exp_rsp.bad ||
                    ({tl_h_i.d_data, tl_h_i.d_user.data_intg} != {exp_rsp.data, exp_rsp.data_intg});

  // W1 sets the tag only if W0 matched as well
  assign tag_wr_req = head_w1 && !mismatch && w0_ok_q;

  // The response integrity is recomputed for a capability store, so it is checked first.
  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(1'b0)
  ) u_tlul_rsp_intg_chk (
    .tl_i (tl_h_i),
    .err_o(rsp_intg_err)
  );

  // A capability store is answered with an acknowledgement from here: right away if it is W0 or
  // failed, and once its tag write is issued if it is a verified W1.
  always_comb begin : proc_own_rsp
    own_rsp          = tlul_pkg::TL_D2H_DEFAULT;
    own_rsp.d_opcode = tlul_pkg::AccessAck;
    if (tag_wr) begin
      own_rsp.d_size   = tag_wr_size_q;
      own_rsp.d_source = tag_wr_source_q;
    end else begin
      own_rsp.d_size   = tl_h_i.d_size;
      own_rsp.d_source = tl_h_i.d_source;
      own_rsp.d_error  = mismatch || (exp_rsp.upper && !w0_ok_q);
    end
  end

  tlul_rsp_intg_gen #(
    .EnableRspIntgGen (1'b1),
    .EnableDataIntgGen(1'b1)
  ) u_tlul_rsp_intg_gen (
    .tl_i(own_rsp),
    .tl_o(own_rsp_intg)
  );

  always_comb begin : proc_connect_tl_rsp
    tl_d_o = tl_h_i;
    if (tag_wr || head_cap) begin
      tl_d_o = own_rsp_intg;
    end
    tl_d_o.d_valid = tag_wr || (tl_h_i.d_valid && !tag_wr_req);
    tl_d_o.a_ready = tl_h_i.a_ready;
  end

  assign rsp_done = tl_d_o.d_valid && tl_d_i.d_ready;
  assign w1_done  = rsp_done && (tag_wr || head_w1);


  ///////////////
  // Tag Write //
  ///////////////

  assign tag_stem = meta_addr_t'({cap_q, 3'b000} - NvmBaseAddr);

  always_comb begin : proc_tag_wr_req
    tl_m_o                  = tlul_pkg::TL_H2D_DEFAULT;
    tl_m_o.a_valid          = tl_h_i.d_valid && tag_wr_req;
    tl_m_o.a_opcode         = tlul_pkg::PutFullData;
    tl_m_o.a_size           = WordSize;
    tl_m_o.a_mask           = '1;
    tl_m_o.a_source         = tl_h_i.d_source;
    tl_m_o.a_address        = MetaNvmTagBase + (addr_t'(tag_stem.meta_word) << 32'd2);
    tl_m_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_m_o);
    tl_m_o.a_user.data_intg = tlul_pkg::get_data_intg(tl_m_o.a_data);
  end

  assign bit_sel_m_o = tag_stem.bit_sel;
  assign tag_wr_done = tl_m_o.a_valid && m_ready_i;
  assign tag_wr_o    = tag_wr;


  //////////////////////////
  // Capability Sequence  //
  //////////////////////////

  assign req_cap = tl_d_i.a_address[AddrWidth-1:3];
  assign tag_wr  = cap_state_q == CapTagWr;

  assign take_w0 = req_done_i && is_w0;
  assign take_w1 = req_done_i && is_w1;

  // The core stores a capability as W0, then W1 of the same capability, and issues nothing else
  // until W1 is answered; its next request may come as W1 is answered. A request that breaks this
  // sequence raises the fatal error, and a capability store that breaks it is also answered with an
  // error and sets no tag. A W0 taken always opens a capability.
  always_comb begin : proc_cap_fsm

    // defaults
    cap_state_d   = cap_state_q;
    seq_violation = 1'b0;

    unique case (cap_state_q)
      CapIdle: begin
        seq_violation = is_w1;
        if (take_w0) begin
          cap_state_d = CapW0;
        end else if (take_w1) begin
          cap_state_d = CapW1;
        end
      end

      // Only the W1 of the capability may follow
      CapW0: begin
        seq_violation = !is_w1 || (req_cap != cap_q);
        if (take_w1) begin
          cap_state_d = CapW1;
        end
      end

      // W1 turns into its tag write, or is answered
      CapW1: begin
        seq_violation = is_w1 || (is_w0 && !w1_done);
        if (take_w0) begin
          cap_state_d = CapW0;
        end else if (tag_wr_done) begin
          cap_state_d = CapTagWr;
        end else if (w1_done) begin
          cap_state_d = CapIdle;
        end
      end

      // W1 is answered once the tag write's response is joined
      CapTagWr: begin
        seq_violation = is_w1 || (is_w0 && !w1_done);
        if (take_w0) begin
          cap_state_d = CapW0;
        end else if (w1_done) begin
          cap_state_d = CapIdle;
        end
      end

      default: begin
        seq_violation = 1'b1;
        cap_state_d   = CapIdle;
      end
    endcase
  end

  // The tag filter hands a request's lookup to the meta port when it is presented,
  // so it could reach the meta port before W1's tag write.
  assign req_before_tag_wr = tl_d_i.a_valid && cap_state_q == CapW1 && !w1_done;

  assign seq_err = (req_done_i && seq_violation) || req_before_tag_wr;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_cap_state
    if (!rst_ni) begin
      cap_state_q <= CapIdle;
    end else begin
      cap_state_q <= cap_state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_cap_addr
    if (!rst_ni) begin
      cap_q <= '0;
    end else begin
      if (take_w0) begin
        cap_q <= req_cap;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_w0_ok
    if (!rst_ni) begin
      w0_ok_q <= 1'b0;
    end else begin
      if (rsp_done && head_w0) begin
        w0_ok_q <= !mismatch;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_tag_wr_rsp
    if (!rst_ni) begin
      tag_wr_size_q   <= '0;
      tag_wr_source_q <= '0;
    end else begin
      if (tag_wr_done) begin
        tag_wr_size_q   <= tl_h_i.d_size;
        tag_wr_source_q <= tl_h_i.d_source;
      end
    end
  end


  ///////////
  // Error //
  ///////////

  assign err_o = (cap_store_i && (cmd_intg_err || (tl_d_i.a_valid && partial_write))) ||
                 (head_cap && rsp_intg_err)                                           ||
                 seq_err;

  // The handshake of the response comes from the NVM or the tag write, the tag only needs the
  // capability's address, and the expect FIFO is never full.
  logic unused_signals;
  assign unused_signals = ^{own_rsp_intg.a_ready, own_rsp_intg.d_valid, tag_stem.rsvd,
                            exp_req_ready};


  ////////////////
  // Assertions //
  ////////////////

  // Only writes are capability stores
  `ASSERT(CapStoreIsWrite_A, tl_d_i.a_valid && cap_store_i |->
                             tl_d_i.a_opcode inside {tlul_pkg::PutFullData,
                                                     tlul_pkg::PutPartialData})

  // The tag filter takes at most NumOutstanding requests before it answers the first
  `ASSERT(ExpFifoNeverFull_A, req_done_i |-> exp_req_ready)

  // Every response taken has its request in the expect FIFO
  `ASSERT(ExpFifoValidOnRsp_A, tl_h_i.d_valid && tl_h_o.d_ready |-> exp_rsp_valid)

  // No request is presented between an unanswered W1 and its tag write: the fork could hand its
  // lookup to the meta port before the tag write, and the lookup would take its response.
  `ASSERT(NoReqBeforeTagWr_A, tl_d_i.a_valid |-> !(cap_state_q == CapW1 && !w1_done))

endmodule
