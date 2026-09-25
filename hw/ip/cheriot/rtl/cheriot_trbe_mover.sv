// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module cheriot_trbe_mover #(
  // TL-UL address type
  parameter type addr_t = logic [top_pkg::TL_AW-1:0],
  // Write address FIFO depth. Bounds the reads in flight: sustaining one word per cycle needs
  // Depth >= read response latency in cycles + 1 (5 covers a response 4 cycles after its request).
  parameter int unsigned WaddrFifoDepth = 32'd5,
  // Words in flight before new reads are held back. The default allows as many unresolved reads as
  // the write address FIFO holds, plus as many invalidation writes waiting for their
  // acknowledgement.
  parameter int unsigned MaxInflight    = 32'd2 * WaddrFifoDepth
)(
  input  logic clk_i,
  input  logic rst_ni,

  // Copy operation
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

  // Error
  output logic err_o
);

  // Types and parameters

  // Byte offset bits of a bus word.
  localparam int unsigned WordOffsetW = $clog2(top_pkg::TL_DBW);

  // Size of a full-word access.
  localparam logic [top_pkg::TL_SZW-1:0] WordSize = top_pkg::TL_SZW'(WordOffsetW);

  localparam int unsigned InflightW = prim_util_pkg::vbits(MaxInflight + 1);

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

  // Signals
  logic issuing;
  logic addr_advance;
  logic start;
  logic is_last_word;

  logic read_a_valid;
  logic read_d_ready;

  logic write_a_valid;
  logic write_a_possible;
  logic write_a_ready;
  logic write_rtag_q;

  logic waddr_fifo_in_valid;
  logic waddr_fifo_in_ready;
  logic waddr_fifo_out_valid;
  logic waddr_fifo_out_ready;
  addr_t waddr_fifo_out;

  // TL-UL response errors, one field per check
  err_t tl_err;

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

  // TLUL requester FSM
  always_comb begin : proc_mover_fsm

    // defaults
    state_d      = state_q;
    current_d    = '0;
    is_last_word = 1'b0;

    unique case (state_q)

      Idle : begin
        if(start) begin
          state_d   = Running;
          current_d = addr_advance ? 'd1 : 'd0;
          if (addr_advance && (current_d == num_words_i)) begin
            is_last_word = 1'b1;
            state_d      = Idle;
            current_d    = '0;
          end
        end
      end

      Running : begin
        current_d = addr_advance ? current_q + 'd1 : current_q;
        if (current_d == num_words_i) begin
          is_last_word = 1'b1;
          state_d      = Idle;
          current_d    = '0;
        end
      end

      default:;
    endcase
  end

  // Copy request handshaking.
  assign ready_o = is_last_word || ((state_q == Idle) && !valid_i);
  assign start   = valid_i && (state_q == Idle);
  assign issuing = (state_q == Running) || start;

  // TL read request port
  always_comb begin : proc_assemble_tl_read_h2d
    tl_r_o                  = tlul_pkg::TL_H2D_DEFAULT;
    tl_r_o.a_size           = WordSize;
    tl_r_o.a_mask           = '1;
    tl_r_o.a_opcode         = tlul_pkg::Get;
    tl_r_o.a_address        = (current_q << WordOffsetW) + start_addr_i;
    tl_r_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_r_o);
    tl_r_o.a_user.data_intg = tlul_pkg::get_data_intg(tl_r_o.a_data);

    // handshake
    tl_r_o.a_valid = read_a_valid && !inflight_full;
    tl_r_o.d_ready = read_d_ready;
  end

  // Stream fork (copy request <-> addr_fifo, tl read a channel)
  stream_fork #(
    .N_OUP(32'd2)
  ) i_stream_fork (
    .clk_i,
    .rst_ni,
    .valid_i(issuing),
    .ready_o(addr_advance),
    .valid_o({waddr_fifo_in_valid, read_a_valid}),
    .ready_i({waddr_fifo_in_ready, tl_r_i.a_ready && tl_r_o.a_valid})
  );

  // Write address FIFO
  prim_fifo_sync #(
    .Width(top_pkg::TL_AW),
    .Depth(WaddrFifoDepth)
  ) i_prim_fifo_sync_waddr (
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

  // Read response handling. A response with an error is marked so it is never invalidated.
  assign payload_fifo_in = '{
    rtag: r_tag_i,
    rerr: tl_err.read_tl || tl_err.read_tl_intg
  };

  prim_fifo_sync #(
    .Width($bits(payload_t)),
    .Depth(32'd2)
  ) i_prim_fifo_sync_payload (
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

  // Read d2h check
  assign tl_err.read_tl = tl_r_i.d_valid                             && (
                        (tl_r_i.d_opcode != tlul_pkg::AccessAckData) ||
                        (tl_r_i.d_error)                             ||
                        (tl_r_i.d_size != WordSize));

  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(1'b1)
  ) i_tlul_rsp_intg_chk_read (
    .tl_i (tl_r_i),
    .err_o(tl_err.read_tl_intg)
  );

  // Write joining
  stream_join_dynamic #(
    .N_INP(32'd2)
  ) i_stream_join_dynamic (
    .inp_valid_i({payload_fifo_out_valid, waddr_fifo_out_valid}),
    .inp_ready_o({payload_fifo_out_ready, waddr_fifo_out_ready}),
    .sel_i      ('1),
    .oup_valid_o(write_a_possible),
    .oup_ready_i(write_a_ready)
  );

  // Store last rtag
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_write_rtag
    if(!rst_ni) begin
      write_rtag_q <= 1'b0;
    end else begin
      if (write_a_possible && write_a_ready) begin
        write_rtag_q <= payload_fifo_out.rtag;
      end
    end
  end

  // We only need a write if certain conditions are met
  assign write_a_valid = write_a_possible       &&
                         !payload_fifo_out.rtag &&
                         !payload_fifo_out.rerr &&
                         write_rtag_q           &&
                         waddr_fifo_out[WordOffsetW];
  assign write_a_ready = write_a_valid ? tl_w_i.a_ready : 1'b1;


  // TL write request port. The write only clears the tag; its data is never written to memory.
  always_comb begin : proc_assemble_tl_write_h2d
    tl_w_o                  = tlul_pkg::TL_H2D_DEFAULT;
    tl_w_o.a_size           = WordSize;
    tl_w_o.a_mask           = '1;
    tl_w_o.a_opcode         = tlul_pkg::PutFullData;
    tl_w_o.a_address        = waddr_fifo_out;
    tl_w_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_w_o);
    tl_w_o.a_user.data_intg = tlul_pkg::get_data_intg(tl_w_o.a_data);

    // handshake
    tl_w_o.a_valid = write_a_valid;
    tl_w_o.d_ready = 1'b1; // no back pressure on write response
  end

  // We only invalidate a tag
  assign w_tag_o = 1'b0;

  // Write d2h check
  assign tl_err.write_tl = tl_w_i.d_valid                         && (
                         (tl_w_i.d_opcode != tlul_pkg::AccessAck) ||
                         (tl_w_i.d_error)                         ||
                         (tl_w_i.d_size != WordSize));

  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(1'b1)
  ) i_tlul_rsp_intg_chk_write (
    .tl_i (tl_w_i),
    .err_o(tl_err.write_tl_intg)
  );

  // Error
  assign err_o = |tl_err;

  // Busy calc
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

  // State storage
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_fsm_state_store
    if(!rst_ni) begin
      state_q <= Idle;
    end else begin
      state_q <= state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_current_element_store
    if(!rst_ni) begin
      current_q <= '0;
    end else begin
      current_q <= current_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_inflight_store
    if(!rst_ni) begin
      inflight_q <= '0;
    end else begin
      inflight_q <= inflight_d;
    end
  end

  // Every resolved word was in flight: no write acknowledgement without a write.
  `ASSERT(InflightNoUnderflow_A, 32'(inflight_q) + 32'(read_issued) >=
                                 32'(word_dropped) + 32'(write_acked))
  `ASSERT(InflightBounded_A, 32'(inflight_q) <= MaxInflight)
  `ASSERT_INIT(MaxInflightNonZero_A, MaxInflight > 0)

endmodule
