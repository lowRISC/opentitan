// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// REQ/ACK synchronizer
//
// This module synchronizes a REQ/ACK handshake across a clock domain crossing.
// Both domains will see a handshake with the duration of one clock cycle.
//
// Notes:
// - Once asserted, the source domain is not allowed to de-assert REQ without ACK.
// - The destination domain is not allowed to send an ACK without a REQ.
// - This module works both when syncing from a faster to a slower clock domain and vice versa.
// - Internally, this module uses a return-to-zero, four-phase handshake protocol. Assuming the
//   destination side responds with an ACK immediately, the latency from asserting the REQ on the
//   source side is:
//   - 1 source + 2 destination clock cycles until the handshake is performed on the
//     destination side,
//   - 1 source + 2 destination + 1 destination + 2 source clock cycles until the handshake is
//     performed on the source side.
//   - It takes another round trip (3 source + 3 destination clock cycles) before the next
//     REQ is starting to be propagated to the destination side. The module is thus not suitable
//     for high-bandwidth communication.

`include "prim_assert.sv"

module prim_sync_reqack (
  input  clk_src_i,       // REQ side, SRC domain
  input  rst_src_ni,      // REQ side, SRC domain
  input  clk_dst_i,       // ACK side, DST domain
  input  rst_dst_ni,      // ACK side, DST domain

  input  logic src_req_i, // REQ side, SRC domain
  output logic src_ack_o, // REQ side, SRC domain
  output logic dst_req_o, // ACK side, DST domain
  input  logic dst_ack_i  // ACK side, DST domain
);

  // Types
  typedef enum logic {
    HANDSHAKE, SYNC
  } sync_reqack_fsm_e;

  // Signals
  sync_reqack_fsm_e src_fsm_ns, src_fsm_cs;
  sync_reqack_fsm_e dst_fsm_ns, dst_fsm_cs;
  logic src_req_d, src_req_q, src_ack;
  logic dst_ack_d, dst_ack_q, dst_req;

  // Move REQ over to ACK side.
  prim_flop_2sync #(
    .Width(1)
  ) req_sync (
    .clk_i  (clk_dst_i),
    .rst_ni (rst_dst_ni),
    .d_i    (src_req_q),
    .q_o    (dst_req)
  );

  // Move ACK over to REQ side.
  prim_flop_2sync #(
    .Width(1)
  ) ack_sync (
    .clk_i  (clk_src_i),
    .rst_ni (rst_src_ni),
    .d_i    (dst_ack_q),
    .q_o    (src_ack)
  );

  // REQ-side FSM (source domain)
  always_comb begin : src_fsm
    src_fsm_ns = src_fsm_cs;

    // By default, we forward the REQ and ACK.
    src_req_d = src_req_i;
    src_ack_o = src_ack;

    unique case (src_fsm_cs)

      HANDSHAKE: begin
        // The handshake on the REQ side is done for exactly 1 clock cycle.
        if (src_req_i && src_ack) begin
          src_fsm_ns = SYNC;
          // Tell ACK side that we are done.
          src_req_d  = 1'b0;
        end
      end

      SYNC: begin
        // Make sure ACK side knows that we are done.
        src_req_d = 1'b0;
        src_ack_o = 1'b0;
        if (!src_ack) begin
          src_fsm_ns = HANDSHAKE;
        end
      end

      default: ;
    endcase
  end

  // ACK-side FSM (destination domain)
  always_comb begin : dst_fsm
    dst_fsm_ns = dst_fsm_cs;

    // By default, we forward the REQ and ACK.
    dst_req_o = dst_req;
    dst_ack_d = dst_ack_i;

    unique case (dst_fsm_cs)

      HANDSHAKE: begin
        // The handshake on the ACK side is done for exactly 1 clock cycle.
        if (dst_req && dst_ack_i) begin
          dst_fsm_ns = SYNC;
        end
      end

      SYNC: begin
        // Don't forward REQ, hold ACK, wait for REQ side.
        dst_req_o  = 1'b0;
        dst_ack_d  = 1'b1;
        if (!dst_req) begin
          dst_fsm_ns = HANDSHAKE;
        end
      end

      default: ;
    endcase
  end

  // Registers
  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_fsm_cs <= HANDSHAKE;
      src_req_q  <= 1'b0;
    end else begin
      src_fsm_cs <= src_fsm_ns;
      src_req_q  <= src_req_d;
    end
  end
  always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
    if (!rst_dst_ni) begin
      dst_fsm_cs <= HANDSHAKE;
      dst_ack_q  <= 1'b0;
    end else begin
      dst_fsm_cs <= dst_fsm_ns;
      dst_ack_q  <= dst_ack_d;
    end
  end

  // Source domain cannot de-assert REQ while waiting for ACK.
  `ASSERT(ReqAckSyncHoldReq, $fell(src_req_i) |-> (src_fsm_cs != HANDSHAKE), clk_src_i, rst_src_ni)

  // Destination domain cannot assert ACK without REQ.
  `ASSERT(ReqAckSyncAckNeedsReq, dst_ack_i |-> dst_req_o, clk_dst_i, rst_dst_ni)

endmodule
