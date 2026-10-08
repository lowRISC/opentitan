// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module cheriot_tbre_mover #(
  // TL-UL address type
  parameter type addr_t = logic [top_pkg::TL_AW-1:0],
  // Words in flight before new reads are held back: unresolved reads plus tag clears waiting for
  // their acknowledgement. Every outstanding read and every outstanding clear carries a source ID
  // of its own.
  parameter int unsigned MaxInflight = 32'd2,
  // Core writes watched at once
  parameter int unsigned NumSnoop    = 32'd1
) (
  input  logic clk_i,
  input  logic rst_ni,

  // Sweep request
  input  addr_t start_addr_i,
  input  addr_t num_words_i,
  input  logic  valid_i,
  output logic  ready_o,
  output logic  busy_o,

  // TL read port
  output tlul_pkg::tl_h2d_t tl_r_o,
  input  logic              r_tag_i,
  input  tlul_pkg::tl_d2h_t tl_r_i,

  // TL write port
  output logic              w_tag_o,
  output tlul_pkg::tl_h2d_t tl_w_o,
  input  tlul_pkg::tl_d2h_t tl_w_i,

  // Core writes. A capability the core writes after its lower word was read is not cleared.
  input  logic  [NumSnoop-1:0] snoop_valid_i,
  input  addr_t [NumSnoop-1:0] snoop_addr_i,

  // Tag clear presented on the write port, until its handshake
  output logic              clear_valid_o,
  output logic              clear_done_o,
  output addr_t             clear_addr_o,

  // Errors: a read answered with an error, whose word is not cleared, and a fault (a write answered
  // with an error, a malformed response or an integrity fault)
  output logic read_err_o,
  output logic err_o
);


  ///////////
  // Types //
  ///////////

  // Byte offset bits of a bus word.
  localparam int unsigned WordOffsetW = $clog2(top_pkg::TL_DBW);

  // Size of a full-word access.
  localparam logic [top_pkg::TL_SZW-1:0] WordSize = top_pkg::TL_SZW'(WordOffsetW);

  // Byte offset bits of a capability.
  localparam int unsigned CapOffsetW = WordOffsetW + 1;

  localparam int unsigned AddrW     = $bits(addr_t);
  localparam int unsigned InflightW = prim_util_pkg::vbits(MaxInflight + 1);
  localparam int unsigned SourceW   = prim_util_pkg::vbits(MaxInflight);

  // Capabilities whose lower word was read and whose upper word is not resolved yet. The words
  // issued and not yet joined are consecutive and at most MaxInflight, so they touch at most
  // MaxInflight / 2 + 1 capabilities; with none of them outstanding, only the capability whose
  // upper word is about to be read is.
  localparam int unsigned TrackDepth = MaxInflight / 2 + 1;
  localparam int unsigned TrackPtrW  = prim_util_pkg::vbits(TrackDepth);

  // Capability-aligned address
  typedef logic [AddrW-1:CapOffsetW] granule_t;

  typedef enum logic {
    Idle,
    Running
  } state_e;

  typedef struct packed {
    logic rtag;
    logic rerr;
  } payload_t;

  typedef struct packed {
    logic read_tl;
    logic read_tl_intg;
    logic write_tl;
    logic write_tl_intg;
  } err_t;

  /////////////
  // Signals //
  /////////////

  logic issuing;
  logic addr_advance;
  logic start;
  logic is_last_word;

  logic read_a_valid;
  logic read_d_ready;

  logic write_a_valid;
  logic write_a_possible;
  logic write_a_ready;
  logic write_rtag_en;
  logic write_rtag_d, write_rtag_q;

  // Source IDs of the next read and of the next tag clear
  logic [SourceW-1:0] read_source_d, read_source_q;
  logic [SourceW-1:0] write_source_d, write_source_q;

  // Capability tracker, oldest capability first, with whether the core wrote it
  granule_t              track_granule_q[TrackDepth];
  logic [TrackDepth-1:0] track_stale_q;
  logic [TrackPtrW-1:0]  track_wptr, track_rptr;
  logic                  track_push;
  logic                  track_pop;

  // The core writes the capability whose lower word is presented on the read port
  logic                  lower_hit_d, lower_hit_q;
  logic                  snoop_read_hit;
  logic [TrackDepth-1:0] snoop_track_hit;
  logic [TrackDepth-1:0] track_frozen;
  logic                  unused_snoop_addr;

  logic waddr_fifo_in_valid;
  logic waddr_fifo_in_ready;
  logic waddr_fifo_out_valid;
  logic waddr_fifo_out_ready;
  addr_t waddr_fifo_out;

  // TL-UL response errors, one field per check
  err_t tl_err;
  logic read_d_err;

  payload_t payload_fifo_in;
  logic payload_fifo_out_valid;
  logic payload_fifo_out_ready;
  payload_t payload_fifo_out;

  addr_t  current_d, current_q;

  // Words in flight
  logic [InflightW-1:0] inflight_d, inflight_q;
  logic                 inflight_full;
  logic                 read_issued;
  logic                 word_dropped;
  logic                 write_acked;

  state_e state_d, state_q;

  ///////////////
  // Sweep FSM //
  ///////////////

  // TLUL requester FSM
  always_comb begin : proc_mover_fsm

    // defaults
    state_d      = state_q;
    current_d    = '0;
    is_last_word = 1'b0;

    unique case (state_q)

      Idle: begin
        if (start) begin
          state_d   = Running;
          current_d = addr_advance ? addr_t'(1) : '0;
          if (addr_advance && (current_d == num_words_i)) begin
            is_last_word = 1'b1;
            state_d      = Idle;
            current_d    = '0;
          end
        end
      end

      Running: begin
        current_d = addr_advance ? current_q + addr_t'(1) : current_q;
        if (current_d == num_words_i) begin
          is_last_word = 1'b1;
          state_d      = Idle;
          current_d    = '0;
        end
      end

      default: ;
    endcase
  end

  // Sweep request handshaking.
  assign ready_o = is_last_word || ((state_q == Idle) && !valid_i);
  assign start   = valid_i && (state_q == Idle);
  assign issuing = (state_q == Running) || start;

  // State storage
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_fsm_state_store
    if (!rst_ni) begin
      state_q <= Idle;
    end else begin
      state_q <= state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_current_element_store
    if (!rst_ni) begin
      current_q <= '0;
    end else begin
      current_q <= current_d;
    end
  end

  ///////////////
  // Read Port //
  ///////////////

  // TL read request port
  always_comb begin : proc_assemble_tl_read_h2d
    tl_r_o                  = tlul_pkg::TL_H2D_DEFAULT;
    tl_r_o.a_size           = WordSize;
    tl_r_o.a_mask           = '1;
    tl_r_o.a_opcode         = tlul_pkg::Get;
    tl_r_o.a_source         = top_pkg::TL_AIW'(read_source_q);
    tl_r_o.a_address        = (current_q << WordOffsetW) + start_addr_i;
    tl_r_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_r_o);
    tl_r_o.a_user.data_intg = tlul_pkg::get_data_intg(tl_r_o.a_data);

    // handshake
    tl_r_o.a_valid = read_a_valid && !inflight_full;
    tl_r_o.d_ready = read_d_ready;
  end

  // Stream fork (sweep request <-> write address FIFO, TL read A channel)
  stream_fork #(
    .N_OUP(32'd2)
  ) u_stream_fork (
    .clk_i,
    .rst_ni,
    .valid_i(issuing),
    .ready_o(addr_advance),
    .valid_o({waddr_fifo_in_valid, read_a_valid}),
    .ready_i({waddr_fifo_in_ready, tl_r_i.a_ready && tl_r_o.a_valid})
  );

  // Write address FIFO
  prim_fifo_sync #(
    .Width(AddrW),
    .Depth(MaxInflight)
  ) u_prim_fifo_sync_waddr (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(waddr_fifo_in_valid),
    .wready_o(waddr_fifo_in_ready),
    .wdata_i ((current_q << WordOffsetW) + start_addr_i),
    .rvalid_o(waddr_fifo_out_valid),
    .rready_i(waddr_fifo_out_ready),
    .rdata_o (waddr_fifo_out),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  // Read response handling. A response with an error is marked so it is never invalidated. The
  // FIFO holds a response for every word in flight, so it never refuses one.
  assign payload_fifo_in = '{
    rtag: r_tag_i,
    rerr: read_d_err || tl_err.read_tl || tl_err.read_tl_intg
  };

  prim_fifo_sync #(
    .Width($bits(payload_t)),
    .Depth(MaxInflight)
  ) u_prim_fifo_sync_payload (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(tl_r_i.d_valid),
    .wready_o(read_d_ready),
    .wdata_i (payload_fifo_in),
    .rvalid_o(payload_fifo_out_valid),
    .rready_i(payload_fifo_out_ready),
    .rdata_o (payload_fifo_out),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  ////////////////
  // Write Port //
  ////////////////

  // Write joining
  stream_join_dynamic #(
    .N_INP(32'd2)
  ) u_stream_join_dynamic (
    .inp_valid_i({payload_fifo_out_valid, waddr_fifo_out_valid}),
    .inp_ready_o({payload_fifo_out_ready, waddr_fifo_out_ready}),
    .sel_i      ('1),
    .oup_valid_o(write_a_possible),
    .oup_ready_i(write_a_ready)
  );

  // Store last rtag
  assign write_rtag_en = write_a_possible && write_a_ready;
  assign write_rtag_d  = payload_fifo_out.rtag && !payload_fifo_out.rerr;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_write_rtag
    if (!rst_ni) begin
      write_rtag_q <= 1'b0;
    end else begin
      if (write_rtag_en) begin
        write_rtag_q <= write_rtag_d;
      end
    end
  end

  // We only need a write if certain conditions are met
  assign write_a_valid = write_a_possible            &&
                         !payload_fifo_out.rtag      &&
                         !payload_fifo_out.rerr      &&
                         write_rtag_q                &&
                         waddr_fifo_out[WordOffsetW] &&
                         !track_stale_q[track_rptr];
  assign write_a_ready = write_a_valid ? tl_w_i.a_ready : 1'b1;

  // TL write request port. The write only clears the tag; its data is never written to memory.
  always_comb begin : proc_assemble_tl_write_h2d
    tl_w_o                  = tlul_pkg::TL_H2D_DEFAULT;
    tl_w_o.a_size           = WordSize;
    tl_w_o.a_mask           = '1;
    tl_w_o.a_opcode         = tlul_pkg::PutFullData;
    tl_w_o.a_source         = top_pkg::TL_AIW'(write_source_q);
    tl_w_o.a_address        = waddr_fifo_out;
    tl_w_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_w_o);
    tl_w_o.a_user.data_intg = tlul_pkg::get_data_intg(tl_w_o.a_data);

    // handshake
    tl_w_o.a_valid = write_a_valid;
    tl_w_o.d_ready = 1'b1; // no back pressure on write response
  end

  // We only invalidate a tag
  assign w_tag_o = 1'b0;

  assign clear_valid_o = tl_w_o.a_valid;
  assign clear_done_o  = tl_w_o.a_valid && tl_w_i.a_ready;
  assign clear_addr_o  = tl_w_o.a_address;

  ////////////////
  // Source IDs //
  ////////////////

  // Both count across sweeps, so a sweep starting while the previous one's words are still in
  // flight cannot reuse an outstanding source ID.
  assign read_source_d  = read_source_q + 1'b1;
  assign write_source_d = write_source_q + 1'b1;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_read_source_store
    if (!rst_ni) begin
      read_source_q <= '0;
    end else begin
      if (read_issued) begin
        read_source_q <= read_source_d;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_write_source_store
    if (!rst_ni) begin
      write_source_q <= '0;
    end else begin
      if (clear_done_o) begin
        write_source_q <= write_source_d;
      end
    end
  end

  ////////////////////////
  // Capability Tracker //
  ////////////////////////

  // Core writes are compared at capability granularity
  always_comb begin : proc_unused_snoop_addr
    unused_snoop_addr = 1'b0;
    for (int unsigned s = 0; s < NumSnoop; s++) begin
      unused_snoop_addr ^= ^snoop_addr_i[s][CapOffsetW-1:0];
    end
  end

  // Capability tracker. A capability enters when its lower word is read and leaves when its upper
  // word is resolved; a core write to it in between marks it stale, and a stale capability is not
  // cleared. The presentation of the lower word counts as well, as parts of its read may reach
  // memory before its handshake completes. The oldest entry no longer changes once its clear is
  // presented; the subsystem watches the clear from there on.
  always_comb begin : proc_snoop_hit
    snoop_read_hit  = 1'b0;
    snoop_track_hit = '0;
    for (int unsigned s = 0; s < NumSnoop; s++) begin
      snoop_read_hit |= snoop_valid_i[s] && snoop_addr_i[s][AddrW-1:CapOffsetW] ==
                                            tl_r_o.a_address[AddrW-1:CapOffsetW];
      for (int unsigned i = 0; i < TrackDepth; i++) begin
        snoop_track_hit[i] |= snoop_valid_i[s] &&
                              (snoop_addr_i[s][AddrW-1:CapOffsetW] == track_granule_q[i]);
      end
    end
  end
  assign track_push     = read_issued && !tl_r_o.a_address[WordOffsetW];
  assign track_pop      = write_a_possible && write_a_ready && waddr_fifo_out[WordOffsetW];

  assign lower_hit_d = tl_r_o.a_valid && !tl_r_o.a_address[WordOffsetW] && !read_issued &&
                       (lower_hit_q || snoop_read_hit);

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_lower_hit_store
    if (!rst_ni) begin
      lower_hit_q <= 1'b0;
    end else begin
      lower_hit_q <= lower_hit_d;
    end
  end

  prim_fifo_sync_cnt #(
    .Depth      (TrackDepth),
    .Secure     (1'b0),
    .NeverClears(1'b1)
  ) u_prim_fifo_sync_cnt_track (
    .clk_i,
    .rst_ni,
    .clr_i      (1'b0),
    .incr_wptr_i(track_push),
    .incr_rptr_i(track_pop),
    .wptr_o     (track_wptr),
    .rptr_o     (track_rptr),
    .full_o     (),
    .empty_o    (),
    .depth_o    (),
    .err_o      ()
  );

  // Each entry is written when its capability enters. A core write marks it stale until it
  // leaves, except once its clear is presented.
  for (genvar i = 0; i < TrackDepth; i++) begin : gen_track_entry
    logic entry_push;
    logic entry_mark;
    logic entry_stale_en;
    logic entry_stale_d;

    assign track_frozen[i] = tl_w_o.a_valid && (track_rptr == TrackPtrW'(unsigned'(i)));
    assign entry_push      = track_push && (track_wptr == TrackPtrW'(unsigned'(i)));
    assign entry_mark      = snoop_track_hit[i] && !track_frozen[i];

    // A capability entering is already stale if the core writes it during its read
    assign entry_stale_en = entry_push || entry_mark;
    assign entry_stale_d  = entry_push ? (lower_hit_q || snoop_read_hit) : 1'b1;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_track_granule_store
      if (!rst_ni) begin
        track_granule_q[i] <= '0;
      end else begin
        if (entry_push) begin
          track_granule_q[i] <= tl_r_o.a_address[AddrW-1:CapOffsetW];
        end
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_track_stale_store
      if (!rst_ni) begin
        track_stale_q[i] <= 1'b0;
      end else begin
        if (entry_stale_en) begin
          track_stale_q[i] <= entry_stale_d;
        end
      end
    end
  end

  ///////////////////////
  // Inflight Tracking //
  ///////////////////////

  // In-flight events
  assign read_issued   = tl_r_o.a_valid && tl_r_i.a_ready;
  assign word_dropped  = write_a_possible && write_a_ready && !write_a_valid;
  assign write_acked   = tl_w_i.d_valid && tl_w_o.d_ready;
  assign inflight_full = (inflight_q == InflightW'(MaxInflight));

  always_comb begin : proc_inflight_count
    inflight_d = inflight_q;
    if (read_issued)  inflight_d = inflight_d + 1'b1;  // word enters
    if (word_dropped) inflight_d = inflight_d - 1'b1;  // resolved at the join, no write needed
    if (write_acked)  inflight_d = inflight_d - 1'b1;  // resolved by its write's acknowledgement
  end

  assign busy_o = (state_q == Running) || (inflight_q != '0);

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_inflight_store
    if (!rst_ni) begin
      inflight_q <= '0;
    end else begin
      inflight_q <= inflight_d;
    end
  end

  ////////////////////
  // Error Handling //
  ////////////////////

  // Read d2h check. A device denies reads, e.g. of a read-protected NVM page, so an error response
  // only fails the sweep.
  assign read_d_err     = tl_r_i.d_valid && tl_r_i.d_error;
  assign tl_err.read_tl = tl_r_i.d_valid && (
                            (tl_r_i.d_opcode != tlul_pkg::AccessAckData) ||
                            (tl_r_i.d_size != WordSize)
                          );

  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(1'b1)
  ) u_tlul_rsp_intg_chk_read (
    .tl_i (tl_r_i),
    .err_o(tl_err.read_tl_intg)
  );

  // Write d2h check
  assign tl_err.write_tl = tl_w_i.d_valid && (
                             (tl_w_i.d_opcode != tlul_pkg::AccessAck) ||
                             tl_w_i.d_error                           ||
                             (tl_w_i.d_size != WordSize)
                           );

  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(1'b1)
  ) u_tlul_rsp_intg_chk_write (
    .tl_i (tl_w_i),
    .err_o(tl_err.write_tl_intg)
  );

  // Errors
  assign read_err_o = read_d_err;
  assign err_o      = |tl_err;

  ////////////////
  // Assertions //
  ////////////////

  // Every resolved word was in flight: no write acknowledgement without a write.
  `ASSERT(InflightNoUnderflow_A, 32'(inflight_q) + 32'(read_issued) >=
                                 32'(word_dropped) + 32'(write_acked))
  `ASSERT(InflightBounded_A, 32'(inflight_q) <= MaxInflight)
  `ASSERT_INIT(MaxInflightNonZero_A, MaxInflight > 0)
  `ASSERT_INIT(NumSnoopNonZero_A, NumSnoop > 0)

  // A sweep covers whole capabilities: the words are paired, and the tracker holds capabilities,
  // by the order of the read stream.
  `ASSERT(SweepCapAligned_A, valid_i |-> start_addr_i[CapOffsetW-1:0] == '0)
  `ASSERT(SweepWholeCaps_A, valid_i |-> num_words_i[0] == 1'b0 && num_words_i != '0)
  // The socket in front of the tag filter adds a port index to the source ID
  `ASSERT_INIT(SourceFits_A, SourceW < top_pkg::TL_AIW)

  // Read responses are never refused, so a clear waiting for the tag filter never blocks them.
  `ASSERT(ReadRspAlwaysAccepted_A, tl_r_i.d_valid |-> read_d_ready)
  // A presented clear is held until its handshake.
  `ASSERT(ClearStable_A, tl_w_o.a_valid && !tl_w_i.a_ready |=>
                         tl_w_o.a_valid && $stable(tl_w_o.a_address) && $stable(tl_w_o.a_source))
  // The tracker holds exactly the capabilities in flight, oldest first.
  `ASSERT(TrackNoOverflow_A, track_push |-> !u_prim_fifo_sync_cnt_track.full_o)
  `ASSERT(TrackNoUnderflow_A, track_pop |-> !u_prim_fifo_sync_cnt_track.empty_o)
  `ASSERT(TrackPopMatches_A, track_pop |->
          track_granule_q[track_rptr] == waddr_fifo_out[AddrW-1:CapOffsetW])

`ifdef INC_ASSERT
  // Responses are paired with requests by order: each port's responses carry the source IDs of its
  // requests in the order they were issued.
  logic [SourceW-1:0] read_rsp_source_d, read_rsp_source_q;
  logic [SourceW-1:0] write_rsp_source_d, write_rsp_source_q;
  logic               read_rsp_done;

  assign read_rsp_done      = tl_r_i.d_valid && tl_r_o.d_ready;
  assign read_rsp_source_d  = read_rsp_source_q + 1'b1;
  assign write_rsp_source_d = write_rsp_source_q + 1'b1;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_read_rsp_source_store
    if (!rst_ni) begin
      read_rsp_source_q <= '0;
    end else begin
      if (read_rsp_done) begin
        read_rsp_source_q <= read_rsp_source_d;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_write_rsp_source_store
    if (!rst_ni) begin
      write_rsp_source_q <= '0;
    end else begin
      if (write_acked) begin
        write_rsp_source_q <= write_rsp_source_d;
      end
    end
  end

  `ASSERT(ReadRspInOrder_A, tl_r_i.d_valid |->
          tl_r_i.d_source == top_pkg::TL_AIW'(read_rsp_source_q))
  `ASSERT(WriteRspInOrder_A, tl_w_i.d_valid |->
          tl_w_i.d_source == top_pkg::TL_AIW'(write_rsp_source_q))
`endif

endmodule
