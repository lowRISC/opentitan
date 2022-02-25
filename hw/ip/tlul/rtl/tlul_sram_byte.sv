// Copyright lowRISC contributors.
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
  parameter bit EnableIntg  = 0,  // Enable integrity handling at byte level
  parameter int Outstanding = 1
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
  output logic error_o
);

  if (EnableIntg) begin : gen_integ_handling

    // state enumeration
    typedef enum logic [1:0] {
      StPassThru,
      StWaitRd,
      StWriteCmd
    } state_e;

    // signal select enumeration
    typedef enum logic [1:0] {
      SelPassThru = 2'b01,
      SelInt = 2'b10
    } sel_sig_e;

    // state and selection
    sel_sig_e sel_int;
    logic stall_host;
    logic wr_phase;
    logic rd_wait;
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
    logic [prim_util_pkg::vbits(Outstanding+1)-1:0] pending_txn_cnt;

    assign a_ack = tl_i.a_valid & tl_o.a_ready;
    assign d_ack = tl_o.d_valid & tl_i.d_ready;
    assign sram_a_ack = tl_sram_o.a_valid & tl_sram_i.a_ready;
    assign sram_d_ack = tl_sram_i.d_valid & tl_sram_o.d_ready;
    assign wr_txn = (tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData);


    assign byte_req_ack = byte_wr_txn & a_ack;
    assign byte_wr_txn = tl_i.a_valid & ~&tl_i.a_mask & wr_txn & ~error_i;
    assign sel_int = (byte_wr_txn || stall_host) ? SelInt : SelPassThru;

    // state machine handling
    always_comb begin
      rd_wait = 1'b0;
      stall_host = 1'b0;
      wr_phase = 1'b0;
      state_d = state_q;

      unique case (state_q)
        StPassThru: begin
          if (byte_req_ack) begin
            state_d = StWaitRd;
          end
        end

        // Due to the way things are serialized, there is no way for the logic to tell which read
        // belongs to the partial read unless it flushes all prior transactions. Hence, we wait
        // here until exactly one outstanding transaction remains (that one is the partial read).
        StWaitRd: begin
          stall_host = 1'b1;
          if (pending_txn_cnt == $bits(pending_txn_cnt)'(1)) begin
            rd_wait    = 1'b1;
            if (sram_d_ack) begin
              state_d = StWriteCmd;
            end
          end
        end

        StWriteCmd: begin
          stall_host = 1'b1;
          wr_phase = 1'b1;

          if (sram_a_ack) begin
            state_d = StPassThru;
          end
        end

        default:;

      endcase // unique case (state_q)

    end

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

    tl_txn_data_t txn_data;
    tl_txn_data_t held_data;
    logic fifo_rdy;
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

    prim_fifo_sync #(
      .Width(TxnDataWidth),
      .Pass(1'b0),
      .Depth(1),
      .OutputZeroIfEmpty(1'b0)
    ) u_sync_fifo (
      .clk_i,
      .rst_ni,
      .clr_i(1'b0),
      .wvalid_i(byte_req_ack),
      .wready_o(fifo_rdy),
      .wdata_i(txn_data),
      .rvalid_o(),
      .rready_i(sram_a_ack),
      .rdata_o(held_data),
      .full_o(),
      .depth_o()
    );

    // captured read data
    logic [top_pkg::TL_DW-1:0] rsp_data;
    always_ff @(posedge clk_i) begin
      if (sram_d_ack && rd_wait) begin
        rsp_data <= tl_sram_i.d_data;
      end
    end

    // internally generated transactions
    tl_h2d_t tl_h2d_int, tl_h2d_intg;

    // while we could simply not assert a_ready to ensure the host keeps
    // the request lines stable, there is no guarantee the hosts (if there are multiple)
    // do not re-arbitrate on every cycle if its transactions are not accepted.
    // As a result, it is better to capture the transaction attributes.
    logic [top_pkg::TL_DW-1:0] combined_data;
    always_comb begin
      for (int i = 0; i < top_pkg::TL_DBW; i++) begin
        combined_data[i*8 +: 8] = held_data.a_mask[i] ?
                                  held_data.a_data[i*8 +: 8] :
                                  rsp_data[i*8 +: 8];
      end
    end

    // Since we are performing a read-modify-write operation,
    // we always access the entire word.
    localparam int AccessSize = $clog2(top_pkg::TL_DBW);
    assign tl_h2d_int = '{
      // use incoming valid as long as we are not stalling the host
      // otherwise look at whether there is a pending write.
      a_valid:   (tl_i.a_valid & ~stall_host) | wr_phase,
      a_opcode:  wr_phase ? PutFullData         : Get,
      a_param:   wr_phase ? held_data.a_param   : tl_i.a_param,  // registered param
      a_size:    top_pkg::TL_SZW'(AccessSize),                   // we always access all bytes
      a_source:  wr_phase ? held_data.a_source  : tl_i.a_source, // registered source
      // registered address, need to use word aligned addresses here.
      a_address: wr_phase ? {held_data.a_address[top_pkg::TL_AW-1:AccessSize], {AccessSize{1'b0}}} :
                            {tl_i.a_address[top_pkg::TL_AW-1:AccessSize], {AccessSize{1'b0}}},
      a_mask:    '{default: '1},
      a_data:    wr_phase ? combined_data       : tl_i.a_data,   // registered data
      a_user:    wr_phase ? held_data.a_user    : tl_i.a_user,   // registered user
      // if we're waiting for an internal read, we force this to 1.
      d_ready:   tl_i.d_ready | rd_wait
    };

    logic unused_held_data;
    assign unused_held_data = ^{held_data.a_address[AccessSize-1:0],
                                held_data.a_size};

    // outgoing tlul transactions
    tlul_cmd_intg_gen #(
      .EnableDataIntgGen(EnableIntg)
    ) u_intg_gen (
      .tl_i(tl_h2d_int),
      .tl_o(tl_h2d_intg)
    );

    assign tl_sram_o = (sel_int == SelInt) ? tl_h2d_intg : tl_i;
    assign error_o = (sel_int == SelInt) ? '0 : error_i;

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
      .depth_o(pending_txn_cnt)
    );

    always_comb begin
      tl_o = tl_sram_i;

      // pass a_ready through directly if we are not stalling
      tl_o.a_ready = tl_sram_i.a_ready & ~stall_host & fifo_rdy & size_fifo_rdy;

      // when internal logic has taken over, do not show response to host during
      // read phase.  During write phase, allow the host to see the completion.
      tl_o.d_valid = tl_sram_i.d_valid & ~rd_wait;

      // the size returned by tl_sram_i does not always correspond to the actual
      // transaction size in cases where a read modify write operation is
      // performed. Hence, we always return the registered size here.
      tl_o.d_size  = a_size;
    end

    // when byte access detected, go to wait read
    `ASSERT(ByteAccessStateChange_A, a_ack & wr_txn & ~&tl_i.a_mask & ~error_i |=>
      state_q inside {StWaitRd})
    // when in wait for read, a successful response should move to write phase
    `ASSERT(ReadCompleteStateChange_A,
        (state_q == StWaitRd) && (pending_txn_cnt == 1) && sram_d_ack |=> state_q == StWriteCmd)

  end else begin : gen_no_integ_handling
    // In this case we pass everything just through.
    assign tl_sram_o = tl_i;
    assign tl_o = tl_sram_i;
    assign error_o = error_i;
  end

endmodule // tlul_adapter_sram
