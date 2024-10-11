// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL adapter for SRAM-like devices
 *
 * This module handles byte writes for tlul integrity.
 * When a byte write is received, the downstream data is read first
 * to correctly create the integrity constant.
 *
 * A tlul transaction goes through this module.  If required, a
 * tlul read transaction is generated out first.  If not required, the
 * incoming tlul transaction is directly muxed out.
 */
module tlul_sram_byte import tlul_pkg::*; #(
  parameter bit EnableIntg     = 0, // Enable integrity handling at byte level,
  parameter int Outstanding    = 1,
  parameter bit EnableReadback = 0  // Enable readback checks on all transactions must have
                                    // EnableIntg == 1 to enable
) (
  input clk_i,
  input rst_ni,

  input tl_h2d_t tl_i,
  output tl_d2h_t tl_o,

  output tl_h2d_t tl_sram_o,
  input tl_d2h_t tl_sram_i,

  // if incoming transaction already has an error, do not
  // attempt to handle the byte-write access.  Instead treat as
  // feedthrough and allow the system to directly error back.
  // The error indication is also fed through
  input error_i,
  output logic error_o,
  output logic alert_o,

  output logic compound_txn_in_progress_o,

  input prim_mubi_pkg::mubi4_t readback_en_i,

  input logic wr_collision_i,
  input logic write_pending_i
);

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::mubi4_test_false_strict;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4Width;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 11 -n 8 \
  //     -s 718546395 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||| (25.45%)
  //  4: |||||||||||||||||||| (36.36%)
  //  5: |||||||||||| (21.82%)
  //  6: ||||||| (12.73%)
  //  7: || (3.64%)
  //  8: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 6
  //
  localparam int StateWidth = 8;
  typedef enum logic [StateWidth-1:0] {
    StPassThru              = 8'b01111110,
    StWaitRd                = 8'b00000010,
    StWriteCmd              = 8'b11110001,
    StWrReadBackInit        = 8'b10011001,
    StWrReadBack            = 8'b00001111,
    StWrReadBackDWait       = 8'b00110000,
    StRdReadBack            = 8'b10101100,
    StRdReadBackDWait       = 8'b11000000,
    StByteWrReadBackInit    = 8'b01010111,
    StByteWrReadBack        = 8'b11100111,
    StByteWrReadBackDWait   = 8'b11111111
  } state_e;

  if (EnableIntg) begin : gen_integ_handling
    // state and selection
    logic stall_host;
    logic wait_phase;
    logic rd_phase;
    logic rd_wait;
    logic wr_phase;
    logic rdback_phase;
    logic rdback_phase_wrreadback;
    logic rdback_wait;
    state_e state_d, state_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        state_q <= StPassThru;
      end else begin
        state_q <= state_d;
      end
    end

    // transaction qualifying signals
    logic a_ack;  // upstream a channel acknowledgement
    logic d_ack;  // upstream d channel acknowledgement
    logic sram_a_ack; // downstream a channel acknowledgement
    logic sram_d_ack; // downstream d channel acknowledgement
    logic wr_txn;
    logic byte_wr_txn;
    logic byte_req_ack;
    logic hold_tx_data;

    localparam int unsigned PendingTxnCntW = prim_util_pkg::vbits(Outstanding+1);
    logic [PendingTxnCntW-1:0] pending_txn_cnt;

    // prim fifo for capturing info
    typedef struct packed {
      logic                  [2:0]  a_param;
      logic  [top_pkg::TL_SZW-1:0]  a_size;
      logic  [top_pkg::TL_AIW-1:0]  a_source;
      logic   [top_pkg::TL_AW-1:0]  a_address;
      logic  [top_pkg::TL_DBW-1:0]  a_mask;
      logic   [top_pkg::TL_DW-1:0]  a_data;
      tl_a_user_t                   a_user;
    } tl_txn_data_t;

    tl_txn_data_t held_data;

    assign a_ack = tl_i.a_valid & tl_o.a_ready;
    assign d_ack = tl_o.d_valid & tl_i.d_ready;
    assign sram_a_ack = tl_sram_o.a_valid & tl_sram_i.a_ready;
    assign sram_d_ack = tl_sram_i.d_valid & tl_sram_o.d_ready;
    assign wr_txn = (tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData);

    assign byte_req_ack = byte_wr_txn & a_ack & ~error_i;
    assign byte_wr_txn = tl_i.a_valid & ~&tl_i.a_mask & wr_txn;

    logic                     rdback_chk_ok;
    mubi4_t                   rdback_check_q, rdback_check_d;
    mubi4_t                   rdback_en_q, rdback_en_d;
    logic [31:0]              rdback_data_exp_q, rdback_data_exp_d;
    logic [DataIntgWidth-1:0] rdback_data_exp_intg_q, rdback_data_exp_intg_d;

    if (EnableReadback) begin : gen_readback_logic
      logic rdback_chk_ok_unbuf;

      assign rdback_chk_ok_unbuf = (rdback_data_exp_q == tl_sram_i.d_data);

      prim_sec_anchor_buf #(
        .Width(1)
      ) u_rdback_chk_ok_buf (
        .in_i (rdback_chk_ok_unbuf),
        .out_o(rdback_chk_ok)
      );

      prim_flop #(
        .Width(MuBi4Width),
        .ResetValue(MuBi4Width'(MuBi4False))
      ) u_rdback_check_flop (
        .clk_i,
        .rst_ni,

        .d_i(MuBi4Width'(rdback_check_d)),
        .q_o({rdback_check_q})
      );

      prim_flop #(
        .Width(MuBi4Width),
        .ResetValue(MuBi4Width'(MuBi4False))
      ) u_rdback_en_flop (
        .clk_i,
        .rst_ni,

        .d_i(MuBi4Width'(rdback_en_d)),
        .q_o({rdback_en_q})
      );

      prim_flop #(
        .Width(32),
        .ResetValue(0)
      ) u_rdback_data_exp (
        .clk_i,
        .rst_ni,

        .d_i(rdback_data_exp_d),
        .q_o(rdback_data_exp_q)
      );

      prim_flop #(
        .Width(DataIntgWidth),
        .ResetValue(0)
      ) u_rdback_data_exp_intg (
        .clk_i,
        .rst_ni,

        .d_i(rdback_data_exp_intg_d),
        .q_o(rdback_data_exp_intg_q)
      );

    // If the readback feature is enabled and we are currently in the readback phase,
    // no address collision should happen inside prim_ram_1p_scr. If this would be the
    // case, we would read from the holding register inside prim_ram_1p_scr instead of
    // actually performing the readback from the memory.
    `ASSERT(WRCollisionDuringReadBack_A, (rdback_phase | rdback_phase_wrreadback) &
        mubi4_test_true_loose(rdback_en_q) |-> !wr_collision_i)


    // If the readback feature is enabled, we assume that the write phase takes one extra cycle
    // due to the underyling scrambling mechanism. If this additional cycle is not needed anymore
    // in the future (e.g. due to the removale of the scrambling mechanism), the readback does not
    // need to be delayed by once cylce in the FSM below.
    `ASSERT(NoPendingWriteAfterWrite_A, wr_phase & mubi4_test_true_loose(rdback_en_q)
        |=> write_pending_i)


    end else begin: gen_no_readback_logic
      assign rdback_chk_ok          = 1'b0;
      assign rdback_check_q         = MuBi4False;
      assign rdback_en_q            = MuBi4False;
      assign rdback_data_exp_q      = 1'b0;
      assign rdback_data_exp_intg_q = 1'b0;

      logic unused_rdback;

      assign unused_rdback = ^{rdback_check_d, rdback_data_exp_d, rdback_data_exp_intg_d};
    end

    // state machine handling
    always_comb begin
      rd_wait = 1'b0;
      wait_phase = 1'b0;
      stall_host = 1'b0;
      wr_phase = 1'b0;
      rd_phase = 1'b0;
      rdback_phase = 1'b0;
      rdback_phase_wrreadback = 1'b0;
      rdback_wait = 1'b0;
      state_d = state_q;
      hold_tx_data = 1'b0;
      alert_o = 1'b0;
      rdback_check_d = rdback_check_q;
      rdback_en_d = rdback_en_q;
      rdback_data_exp_d  = rdback_data_exp_q;
      rdback_data_exp_intg_d  = rdback_data_exp_intg_q;

      unique case (state_q)
        StPassThru: begin
          if (mubi4_test_true_loose(rdback_en_q) && mubi4_test_true_loose(rdback_check_q)) begin
            // When we're expecting a readback check that means we'll see a data response from the
            // SRAM this cycle which we need to check against the readback registers. During this
            // cycle the data response out (via tl_o) will be squashed to invalid but we can accept
            // a new transaction (via tl_i).
            rdback_wait    = 1'b1;
            rdback_check_d = MuBi4False;

            // Perform the readback check.
            if (!rdback_chk_ok) begin
              alert_o = 1'b1;
            end
          end

          if (byte_wr_txn) begin
            rd_phase = 1'b1;
            if (byte_req_ack) begin
              state_d = StWaitRd;
            end
          end else if (a_ack && mubi4_test_true_loose(rdback_en_q) && !error_i) begin
            // For reads and full word writes we'll first do the transaction and then do a readback
            // check. Setting `hold_tx_data` here will preserve the transaction information in
            // u_sync_fifo for doing the readback transaction.
            hold_tx_data = 1'b1;
            state_d      = wr_txn ? StWrReadBackInit : StRdReadBack;
          end

          if (!tl_sram_o.a_valid && !tl_o.d_valid &&
              mubi4_test_false_strict(rdback_check_q)) begin
            // Store readback enable into register when bus is idle and no readback is processed.
            rdback_en_d = readback_en_i;
          end
        end

        // Due to the way things are serialized, there is no way for the logic to tell which read
        // belongs to the partial read unless it flushes all prior transactions. Hence, we wait
        // here until exactly one outstanding transaction remains (that one is the partial read).
        StWaitRd: begin
          rd_phase = 1'b1;
          stall_host = 1'b1;
          if (pending_txn_cnt == PendingTxnCntW'(1)) begin
            rd_wait = 1'b1;
            if (sram_d_ack) begin
              state_d = StWriteCmd;
            end
          end
        end

        StWriteCmd: begin
          stall_host = 1'b1;
          wr_phase = 1'b1;

          if (sram_a_ack) begin
            state_d = mubi4_test_true_loose(rdback_en_q) ? StByteWrReadBackInit : StPassThru;
            rdback_check_d         = mubi4_test_true_loose(rdback_en_q) ? MuBi4True : MuBi4False;
            rdback_data_exp_d      = tl_sram_o.a_data;
            rdback_data_exp_intg_d = tl_sram_o.a_user.data_intg;
          end
        end

        StWrReadBackInit: begin
          // Perform readback after full write. To avoid that we read the holding register
          // in the readback, wait until the write was processed by the memory module.
          if (EnableReadback == 0) begin : gen_inv_state_StWrReadBackInit
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          // Stall the host to perform the readback in the next cycle.
          stall_host = 1'b1;

          // Need to ensure there's no other transactions in flight before we do the readback (the
          // initial write we're doing the readback for should be the only one active).
          if (pending_txn_cnt == PendingTxnCntW'(1)) begin
            wait_phase  = 1'b1;
            // Data we're checking against the readback is captured from the write transaction that
            // was sent.
            rdback_check_d         = mubi4_test_true_loose(rdback_en_q) ? MuBi4True : MuBi4False;
            rdback_data_exp_d      = held_data.a_data;
            rdback_data_exp_intg_d = held_data.a_user.data_intg;
            if (d_ack) begin
              // Got an immediate TL-UL write response. Wait for one cycle until the holding
              // register is flushed and then perform the readback.
              state_d = StWrReadBack;
            end else  begin
              // No response yet to the initial write.
              state_d = StWrReadBackDWait;
            end
          end
        end

        StWrReadBack: begin
          // Perform readback and check response in StPassThru.
          if (EnableReadback == 0) begin : gen_inv_state_StWrReadBack
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          stall_host = 1'b1;

          rdback_phase = 1'b1;

          state_d = StPassThru;
        end

        StWrReadBackDWait: begin
          // We have not received the d_valid response of the initial write. Wait
          // for the valid signal.
          if (EnableReadback == 0) begin : gen_inv_state_StWrReadBackDWait
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          // Wait until we get write response.
          wait_phase  = 1'b1;

          stall_host = 1'b1;

          if (d_ack) begin
            // Got the TL-UL write response. Wait for one cycle until the holding
            // register is flushed and then perform the readback.
            state_d = StWrReadBack;
          end
        end

        StByteWrReadBackInit: begin
          // Perform readback after partial write. To avoid that we read the holding register
          // in the readback, do the actual readback check in the next FSM state.
          if (EnableReadback == 0) begin : gen_inv_state_StByteWrReadBackInit
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          // Sends out a read to a readback check on a partial write. The host is stalled whilst
          // this is happening.
          stall_host = 1'b1;

          // Wait until there is a single ongoing transaction.
          if (pending_txn_cnt == PendingTxnCntW'(1)) begin
            // Wait for one cycle with sending readback request to SRAM to avoid reading from
            // holding register.
            wait_phase  = 1'b1;

            if (d_ack) begin
              // Got an immediate TL-UL write response. Wait for one cycle until the holding
              // register is flushed and then perform the readback.
              state_d = StByteWrReadBack;
            end else begin
              // No response received for initial write. We already can send the
              // request for the readback in the next cycle but we need to wait
              // for the response for the initial write before doing the readback
              // check.
              state_d = StByteWrReadBackDWait;
            end
          end
        end

        StByteWrReadBack: begin
          // Wait until the memory module has completed the partial write.
          // Perform readback and check response in StPassThru.
          if (EnableReadback == 0) begin : gen_inv_state_StByteWrReadBack
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          stall_host = 1'b1;

          rdback_phase_wrreadback = 1'b1;

          state_d = StPassThru;
        end

        StByteWrReadBackDWait: begin
          if (EnableReadback == 0) begin : gen_inv_state_StByteWrReadBackDWait
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          stall_host = 1'b1;

          // Wait for one cycle with sending readback request to SRAM.
          wait_phase  = 1'b1;

          if (d_ack) begin
            // Got the TL-UL write response. Wait for one cycle until the holding
            // register is flushed and then perform the readback.
            state_d = StByteWrReadBack;
          end
        end

        StRdReadBack: begin
          if (EnableReadback == 0) begin : gen_inv_state_StRdReadBack
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          // Sends out a read to a readback check on a read. The host is stalled whilst
          // this is happening.
          stall_host = 1'b1;

          // Need to ensure there's no other transactions in flight before we do the readback (the
          // read we're doing the readback for should be the only one active).
          if (pending_txn_cnt == PendingTxnCntW'(1)) begin
            rdback_phase = 1'b1;

            if (d_ack) begin
              state_d                = StPassThru;
              // Data for the readback check comes from the first read.
              rdback_check_d         = mubi4_test_true_loose(rdback_en_q) ? MuBi4True : MuBi4False;
              rdback_data_exp_d      = tl_o.d_data;
              rdback_data_exp_intg_d = tl_o.d_user.data_intg;
            end else  begin
              // No response yet to the initial read, so go wait for it.
              state_d = StRdReadBackDWait;
            end
          end
        end

        StRdReadBackDWait : begin
          if (EnableReadback == 0) begin : gen_inv_state_StRdReadBackDWait
            // If readback is disabled, we shouldn't be in this state.
            alert_o = 1'b1;
          end

          stall_host = 1'b1;

          if (d_ack) begin
            // Response received for first read. Now need to await data for the readback check
            // which is done in the `StPassThru` state.
            state_d                = StPassThru;
            // Data for the readback check comes from the first read.
            rdback_check_d         = mubi4_test_true_loose(rdback_en_q) ? MuBi4True : MuBi4False;
            rdback_data_exp_d      = tl_o.d_data;
            rdback_data_exp_intg_d = tl_o.d_user.data_intg;
          end
        end

        default: begin
          alert_o = 1'b1;
        end
      endcase // unique case (state_q)

    end

    tl_txn_data_t txn_data;
    logic fifo_rdy;
    logic txn_data_wr;
    localparam int TxnDataWidth = $bits(tl_txn_data_t);

    assign txn_data = '{
      a_param: tl_i.a_param,
      a_size: tl_i.a_size,
      a_source: tl_i.a_source,
      a_address: tl_i.a_address,
      a_mask: tl_i.a_mask,
      a_data: tl_i.a_data,
      a_user: tl_i.a_user
    };


    assign txn_data_wr = hold_tx_data | byte_req_ack;

    prim_fifo_sync #(
      .Width(TxnDataWidth),
      .Pass(1'b0),
      .Depth(1),
      .OutputZeroIfEmpty(1'b0)
    ) u_sync_fifo (
      .clk_i,
      .rst_ni,
      .clr_i(1'b0),
      .wvalid_i(txn_data_wr),
      .wready_o(fifo_rdy),
      .wdata_i(txn_data),
      .rvalid_o(),
      .rready_i(sram_a_ack),
      .rdata_o(held_data),
      .full_o(),
      .depth_o(),
      .err_o()
    );

    // captured read data
    logic [top_pkg::TL_DW-1:0] rsp_data;
    always_ff @(posedge clk_i) begin
      if (sram_d_ack && rd_wait) begin
        rsp_data <= tl_sram_i.d_data;
      end
    end

    // while we could simply not assert a_ready to ensure the host keeps
    // the request lines stable, there is no guarantee the hosts (if there are multiple)
    // do not re-arbitrate on every cycle if its transactions are not accepted.
    // As a result, it is better to capture the transaction attributes.
    logic [top_pkg::TL_DW-1:0] combined_data, unused_data;
    always_comb begin
      for (int i = 0; i < top_pkg::TL_DBW; i++) begin
        combined_data[i*8 +: 8] = held_data.a_mask[i] ?
                                  held_data.a_data[i*8 +: 8] :
                                  rsp_data[i*8 +: 8];
      end
    end

    // Compute updated integrity bits for the data.
    // Note that the CMD integrity does not have to be correct, since it is not consumed nor
    // checked further downstream.
    logic [tlul_pkg::DataIntgWidth-1:0] data_intg;

    tlul_data_integ_enc u_tlul_data_integ_enc (
      .data_i(combined_data),
      .data_intg_o({data_intg, unused_data})
    );

    tl_a_user_t combined_user;
    always_comb begin
      combined_user           = held_data.a_user;
      combined_user.data_intg = data_intg;
    end

    localparam int unsigned AccessSize = $clog2(top_pkg::TL_DBW);
    always_comb begin
      // Pass-through by default
      tl_sram_o = tl_i;
      // If we're waiting for an internal read for RMW, or a readback read, we force this to 1.
      tl_sram_o.d_ready = tl_i.d_ready | rd_wait | rdback_wait;

      // We take over the TL-UL bus if there is a pending read or write for the RMW transaction.
      // TL-UL signals are selectively muxed below to reduce complexity and remove long timing
      // paths through the error_i signal. In particular, we avoid creating paths from error_i
      // to the address and data output since these may feed into RAM scrambling logic further
      // downstream.

      // Write transactions for RMW or reads when in readback mode.
      if (wr_phase | rdback_phase | rdback_phase_wrreadback) begin
        tl_sram_o.a_valid   = 1'b1;
        // During a read-modify write, always access the entire word.
        tl_sram_o.a_opcode  = wr_phase ? PutFullData : Get;
        // In either read-modify write or SRAM readback mode, use the mask, size and address
        // of the original request.
        tl_sram_o.a_size =
            (wr_phase | rdback_phase_wrreadback) ? top_pkg::TL_SZW'(AccessSize) : held_data.a_size;
        tl_sram_o.a_mask =
            (wr_phase | rdback_phase_wrreadback) ? '{default: '1}               : held_data.a_mask;
        // override with held / combined data.
        // need to use word aligned addresses here.
        tl_sram_o.a_address = held_data.a_address;
        tl_sram_o.a_address[AccessSize-1:0] =
            (wr_phase | rdback_phase_wrreadback) ? '0 : held_data.a_address[AccessSize-1:0];
        tl_sram_o.a_source  = held_data.a_source;
        tl_sram_o.a_param   = held_data.a_param;
        tl_sram_o.a_data    = wr_phase ? combined_data : '0;
        tl_sram_o.a_user    = wr_phase ? combined_user : '0;
      // Read transactions for RMW.
      end else if (rd_phase) begin
        // need to use word aligned addresses here.
        tl_sram_o.a_address[AccessSize-1:0] = '0;
        // Only override the control signals if there is no error at the input.
        if (!error_i || stall_host) begin
          // Since we are performing a read-modify-write operation,
          // we always access the entire word.
          tl_sram_o.a_size    = top_pkg::TL_SZW'(AccessSize);
          tl_sram_o.a_mask    = '{default: '1};
          // use incoming valid as long as we are not stalling the host
          tl_sram_o.a_valid   = tl_i.a_valid & ~stall_host;
          tl_sram_o.a_opcode  = Get;
        end
      end else if (wait_phase) begin
        // Delay the readback request to avoid that we are reading the holding
        // register.
        tl_sram_o.a_valid = 1'b0;
      end
    end

    // This assert is necessary for the casting of AccessSize.
    `ASSERT(TlulSramByteTlSize_A, top_pkg::TL_SZW >= $clog2(AccessSize + 1))

    assign error_o = error_i & ~stall_host;

    logic size_fifo_rdy;
    logic [top_pkg::TL_SZW-1:0] a_size;
    prim_fifo_sync #(
      .Width(top_pkg::TL_SZW),
      .Pass(1'b0),
      .Depth(Outstanding),
      .OutputZeroIfEmpty(1'b1)
    ) u_sync_fifo_a_size (
      .clk_i,
      .rst_ni,
      .clr_i(1'b0),
      .wvalid_i(a_ack),
      .wready_o(size_fifo_rdy),
      .wdata_i(tl_i.a_size),
      .rvalid_o(),
      .rready_i(d_ack),
      .rdata_o(a_size),
      .full_o(),
      .depth_o(pending_txn_cnt),
      .err_o()
    );

    always_comb begin
      tl_o = tl_sram_i;

      // pass a_ready through directly if we are not stalling
      tl_o.a_ready = tl_sram_i.a_ready & ~stall_host & fifo_rdy & size_fifo_rdy;

      // when internal logic has taken over, do not show response to host during
      // read phase.  During write phase, allow the host to see the completion.
      tl_o.d_valid = tl_sram_i.d_valid & ~rd_wait & ~rdback_wait;

      // the size returned by tl_sram_i does not always correspond to the actual
      // transaction size in cases where a read modify write operation is
      // performed. Hence, we always return the registered size here.
      tl_o.d_size  = a_size;
    end // always_comb

    // unused info from tl_sram_i
    // see explanation in above block
    logic unused_tl;
    assign unused_tl = |tl_sram_i.d_size;

    // when byte access detected, go to wait read
    `ASSERT(ByteAccessStateChange_A, a_ack & wr_txn & ~&tl_i.a_mask & ~error_i |=>
      state_q inside {StWaitRd})
    // when in wait for read, a successful response should move to write phase
    `ASSERT(ReadCompleteStateChange_A,
        (state_q == StWaitRd) && (pending_txn_cnt == 1) && sram_d_ack |=> state_q == StWriteCmd)
    // The readback logic assumes that any request on the readback channel will be instantly granted
    // (i.e. after the initial SRAM read or write request from the external requester has been
    // granted). This helps simplify the logic. It is guaranteed when connected to an SRAM as it
    // produces no back pressure. When connected to a scrambled SRAM the key going invalid will
    // cause a_ready to drop. The `compound_txn_in_progress_o` output is provided for this scenario.
    // When asserted SRAM should not drop `a_ready` even if there is an invalid scrambling key.
    `ASSERT(ReadbackAccessAlwaysGranted_A, (rdback_phase | rdback_phase_wrreadback) && !error_i
      |-> tl_sram_i.a_ready)

    // The readback logic assumes the result of a read transaction issues for the readback will get
    // an immediate response. This can be guaranteed when connected to a SRAM, see above comment.
    `ASSERT(ReadbackDataImmediatelyAvailable_A, (state_q == StPassThru) &&
      mubi4_test_true_loose(rdback_en_q) && mubi4_test_true_loose(rdback_check_q) &&
      !error_i|-> tl_sram_i.d_valid)

    assign compound_txn_in_progress_o = wr_phase | rdback_phase | rdback_phase_wrreadback;
  end else begin : gen_no_integ_handling
    // In this case we pass everything just through.
    assign tl_sram_o = tl_i;
    assign tl_o = tl_sram_i;
    assign error_o = error_i;
    assign alert_o = 1'b0;
    assign compound_txn_in_progress_o = 1'b0;

    // Signal only used in readback mode.
    mubi4_t unused_readback_en;
    assign unused_readback_en = readback_en_i;

  end

  // Signals only used for SVA.
  logic unused_write_pending, unused_wr_collision;
  assign unused_write_pending = write_pending_i;
  assign unused_wr_collision = wr_collision_i;

  // EnableReadback requires that EnableIntg is on.
  // EnableIntg can be used without EnableReadback.
  `ASSERT_INIT(SramReadbackAndIntg,
      (EnableReadback && EnableIntg) || (!EnableReadback && (EnableIntg || !EnableIntg)))
endmodule // tlul_adapter_sram
