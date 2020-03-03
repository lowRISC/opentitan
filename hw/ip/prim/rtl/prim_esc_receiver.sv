// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module decodes escalation enable pulses that have been encoded using
// the prim_esc_sender module.
//
// The module supports in-band ping testing of the escalation
// wires. This is accomplished by the sender module that places a single-cycle,
// differentially encoded pulse on esc_p/n which will be interpreted as a ping
// request by the receiver module. The receiver module responds by sending back
// the response pattern "1010".
//
// Native escalation enable pulses are differentiated from ping
// requests by making sure that these pulses are always longer than 1 cycle.
//
// See also: prim_esc_sender, prim_diff_decode, alert_handler

`include "prim_assert.sv"

module prim_esc_receiver
  import prim_esc_pkg::*;
(
  input           clk_i,
  input           rst_ni,
  // escalation enable
  output logic    esc_en_o,
  // escalation / ping response
  output esc_rx_t esc_rx_o,
  // escalation output diff pair
  input esc_tx_t  esc_tx_i
);

  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////

  logic esc_level, sigint_detected;

  prim_diff_decode #(
    .AsyncOn(1'b0)
  ) i_decode_esc (
    .clk_i,
    .rst_ni,
    .diff_pi  ( esc_tx_i.esc_p  ),
    .diff_ni  ( esc_tx_i.esc_n  ),
    .level_o  ( esc_level       ),
    .rise_o   (                 ),
    .fall_o   (                 ),
    .event_o  (                 ),
    .sigint_o ( sigint_detected )
  );

  /////////////////
  // RX/TX Logic //
  /////////////////

  typedef enum logic [2:0] {Idle, Check, PingResp, EscResp, SigInt} state_e;
  state_e state_d, state_q;
  logic resp_pd, resp_pq, resp_nd, resp_nq;

  assign esc_rx_o.resp_p = resp_pq;
  assign esc_rx_o.resp_n = resp_nq;


  always_comb begin : p_fsm
    // default
    state_d  = state_q;
    resp_pd  = 1'b0;
    resp_nd  = 1'b1;
    esc_en_o = 1'b0;

    unique case (state_q)
      // wait for the esc_p/n diff pair
      Idle: begin
        if (esc_level) begin
          state_d = Check;
          resp_pd = 1'b1;
          resp_nd = 1'b0;
        end
      end
      // we decide here whether this is only a ping request or
      // whether this is an escalation enable
      Check: begin
        state_d = PingResp;
        if (esc_level) begin
          state_d  = EscResp;
          esc_en_o = 1'b1;
        end
      end
      // finish ping response. in case esc_level is again asserted,
      // we got an escalation signal (pings cannot occur back to back)
      PingResp: begin
        state_d = Idle;
        resp_pd = 1'b1;
        resp_nd = 1'b0;
        if (esc_level) begin
          state_d  = EscResp;
          esc_en_o = 1'b1;
        end
      end
      // we have got an escalation enable pulse,
      // keep on toggling the outputs
      EscResp: begin
        state_d = Idle;
        if (esc_level) begin
          state_d  = EscResp;
          resp_pd  = ~resp_pq;
          resp_nd  = resp_pq;
          esc_en_o = 1'b1;
        end
      end
      // we have a signal integrity issue at one of
      // the incoming diff pairs. this condition is
      // signalled to the sender by setting the resp
      // diffpair to the same value and continuously
      // toggling them.
      SigInt: begin
        state_d = Idle;
        if (sigint_detected) begin
          state_d = SigInt;
          resp_pd = ~resp_pq;
          resp_nd = ~resp_pq;
        end
      end
      default : state_d = Idle;
    endcase

    // bail out if a signal integrity issue has been detected
    if (sigint_detected && (state_q != SigInt)) begin
      state_d  = SigInt;
      resp_pd  = 1'b0;
      resp_nd  = 1'b0;
    end
  end


  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= Idle;
      resp_pq <= 1'b0;
      resp_nq <= 1'b1;
    end else begin
      state_q <= state_d;
      resp_pq <= resp_pd;
      resp_nq <= resp_nd;
    end
  end

  ////////////////
  // assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(EscEnKnownO_A, esc_en_o)
  `ASSERT_KNOWN(RespPKnownO_A, esc_rx_o)

  `ASSERT(SigIntCheck0_A, esc_tx_i.esc_p == esc_tx_i.esc_n |=>
      esc_rx_o.resp_p == esc_rx_o.resp_n, clk_i, !rst_ni)
  `ASSERT(SigIntCheck1_A, esc_tx_i.esc_p == esc_tx_i.esc_n |=> state_q == SigInt)
  // correct diff encoding
  `ASSERT(DiffEncCheck_A, esc_tx_i.esc_p ^ esc_tx_i.esc_n |=>
      esc_rx_o.resp_p ^ esc_rx_o.resp_n)
  // disable in case of ping integrity issue
  `ASSERT(PingRespCheck_A, $rose(esc_tx_i.esc_p) |=> $fell(esc_tx_i.esc_p) |->
      $rose(esc_rx_o.resp_p) |=> $fell(esc_rx_o.resp_p),
      clk_i, !rst_ni || (esc_tx_i.esc_p == esc_tx_i.esc_n))
  // escalation response needs to continuously toggle
  `ASSERT(EscRespCheck_A, esc_tx_i.esc_p && $past(esc_tx_i.esc_p) &&
      (esc_tx_i.esc_p ^ esc_tx_i.esc_n) && $past(esc_tx_i.esc_p ^ esc_tx_i.esc_n)
      |=> esc_rx_o.resp_p != $past(esc_rx_o.resp_p))
  // detect escalation pulse
  `ASSERT(EscEnCheck_A, esc_tx_i.esc_p && (esc_tx_i.esc_p ^ esc_tx_i.esc_n) && state_q != SigInt
      |=> esc_tx_i.esc_p && (esc_tx_i.esc_p ^ esc_tx_i.esc_n) |-> esc_en_o)

endmodule : prim_esc_receiver
