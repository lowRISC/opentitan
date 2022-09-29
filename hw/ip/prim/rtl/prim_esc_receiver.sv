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
#(
  // The number of escalation severities. Should be set to the Alert Handler's N_ESC_SEV when this
  // primitive is instantiated.
  parameter int N_ESC_SEV = 4,

  // The width of the Alert Handler's ping counter. Should be set to the Alert Handler's PING_CNT_DW
  // when this primitive is instantiated.
  parameter int PING_CNT_DW = 16,

  // This counter monitors incoming ping requests and auto-escalates if the alert handler
  // ceases to send them regularly. The maximum number of cycles between subsequent ping requests
  // is N_ESC_SEV x (2 x 2 x 2**PING_CNT_DW), see also implementation of the ping timer
  // (alert_handler_ping_timer.sv). The timeout counter below uses a timeout that is 4x larger than
  // that in order to incorporate some margin.
  //
  // Do NOT modify this counter value, when instantiating it in the design. It is only exposed to
  // reduce the state space in the FPV testbench.
  localparam int MarginFactor = 4,
  localparam int NumWaitCounts = 2,
  localparam int NumTimeoutCounts = 2,
  parameter int TimeoutCntDw = $clog2(MarginFactor) +
                               $clog2(N_ESC_SEV) +
                               $clog2(NumWaitCounts) +
                               $clog2(NumTimeoutCounts) +
                               PING_CNT_DW
) (
  input           clk_i,
  input           rst_ni,
  // escalation enable
  output logic    esc_req_o,
  // escalation / ping response
  output esc_rx_t esc_rx_o,
  // escalation output diff pair
  input esc_tx_t  esc_tx_i
);

  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////

  logic esc_level, esc_p, esc_n, sigint_detected;

  // This prevents further tool optimizations of the differential signal.
  prim_buf #(
    .Width(2)
  ) u_prim_buf_esc (
    .in_i({esc_tx_i.esc_n,
           esc_tx_i.esc_p}),
    .out_o({esc_n,
            esc_p})
  );

  prim_diff_decode #(
    .AsyncOn(1'b0)
  ) u_decode_esc (
    .clk_i,
    .rst_ni,
    .diff_pi  ( esc_p           ),
    .diff_ni  ( esc_n           ),
    .level_o  ( esc_level       ),
    .rise_o   (                 ),
    .fall_o   (                 ),
    .event_o  (                 ),
    .sigint_o ( sigint_detected )
  );

  ////////////////////////////////////////////
  // Ping Monitor Counter / Auto Escalation //
  ////////////////////////////////////////////

  // The timeout counter is kicked off when the first ping occurs, and subsequent pings reset
  // the counter to 1. The counter keeps on counting when it is nonzero, and saturates when it
  // has reached its maximum (this state is terminal).
  logic ping_en, timeout_cnt_error;
  logic timeout_cnt_set, timeout_cnt_en;
  logic [TimeoutCntDw-1:0] timeout_cnt;
  assign timeout_cnt_set = (ping_en && !(&timeout_cnt));
  assign timeout_cnt_en = ((timeout_cnt > '0) && !(&timeout_cnt));

  prim_count #(
    .Width(TimeoutCntDw),
    // The escalation receiver behaves differently than other comportable IP. I.e., instead of
    // sending out an alert signal, this condition is handled internally in the alert handler.
    .EnableAlertTriggerSVA(0)
  ) u_prim_count (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(timeout_cnt_set),
    .set_cnt_i(TimeoutCntDw'(1)),
    .incr_en_i(timeout_cnt_en),
    .decr_en_i(1'b0),
    .step_i(TimeoutCntDw'(1)),
    .cnt_o(timeout_cnt),
    .cnt_next_o(),
    .err_o(timeout_cnt_error)
  );

  // Escalation is asserted if
  // - requested via the escalation sender/receiver path,
  // - the ping monitor timeout is reached,
  // - the two ping monitor counters are in an inconsistent state.
  logic esc_req;
  prim_sec_anchor_buf #(
    .Width(1)
  ) u_prim_buf_esc_req (
    .in_i(esc_req || (&timeout_cnt) || timeout_cnt_error),
    .out_o(esc_req_o)
  );

  /////////////////
  // RX/TX Logic //
  /////////////////

  typedef enum logic [2:0] {Idle, Check, PingResp, EscResp, SigInt} state_e;
  state_e state_d, state_q;
  logic resp_pd, resp_pq;
  logic resp_nd, resp_nq;

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_flop #(
    .Width(2),
    .ResetValue(2'b10)
  ) u_prim_flop_esc (
    .clk_i,
    .rst_ni,
    .d_i({resp_nd, resp_pd}),
    .q_o({resp_nq, resp_pq})
  );

  assign esc_rx_o.resp_p = resp_pq;
  assign esc_rx_o.resp_n = resp_nq;

  always_comb begin : p_fsm
    // default
    state_d = state_q;
    resp_pd = 1'b0;
    resp_nd = 1'b1;
    esc_req = 1'b0;
    ping_en = 1'b0;

    unique case (state_q)
      // wait for the esc_p/n diff pair
      Idle: begin
        if (esc_level) begin
          state_d = Check;
          resp_pd = ~resp_pq;
          resp_nd = resp_pq;
        end
      end
      // we decide here whether this is only a ping request or
      // whether this is an escalation enable
      Check: begin
        state_d = PingResp;
        resp_pd = ~resp_pq;
        resp_nd = resp_pq;
        if (esc_level) begin
          state_d = EscResp;
          esc_req = 1'b1;
        end
      end
      // finish ping response. in case esc_level is again asserted,
      // we got an escalation signal (pings cannot occur back to back)
      PingResp: begin
        state_d = Idle;
        resp_pd = ~resp_pq;
        resp_nd = resp_pq;
        ping_en = 1'b1;
        if (esc_level) begin
          state_d = EscResp;
          esc_req = 1'b1;
        end
      end
      // we have got an escalation enable pulse,
      // keep on toggling the outputs
      EscResp: begin
        state_d = Idle;
        if (esc_level) begin
          state_d = EscResp;
          resp_pd = ~resp_pq;
          resp_nd = resp_pq;
          esc_req = 1'b1;
        end
      end
      // we have a signal integrity issue at one of
      // the incoming diff pairs. this condition is
      // signalled to the sender by setting the resp
      // diffpair to the same value and continuously
      // toggling them.
      SigInt: begin
        state_d = Idle;
        esc_req = 1'b1;
        if (sigint_detected) begin
          state_d = SigInt;
          resp_pd = ~resp_pq;
          resp_nd = ~resp_pq;
        end
      end
      default: state_d = Idle;
    endcase

    // bail out if a signal integrity issue has been detected
    if (sigint_detected && (state_q != SigInt)) begin
      state_d = SigInt;
      resp_pd = 1'b0;
      resp_nd = 1'b0;
    end
  end


  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= Idle;
    end else begin
      state_q <= state_d;
    end
  end

  ////////////////
  // assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(EscEnKnownO_A, esc_req_o)
  `ASSERT_KNOWN(RespPKnownO_A, esc_rx_o)

  `ASSERT(SigIntCheck0_A, esc_tx_i.esc_p == esc_tx_i.esc_n |=> esc_rx_o.resp_p == esc_rx_o.resp_n)
  `ASSERT(SigIntCheck1_A, esc_tx_i.esc_p == esc_tx_i.esc_n |=> state_q == SigInt)
  // auto-escalate in case of signal integrity issue
  `ASSERT(SigIntCheck2_A, esc_tx_i.esc_p == esc_tx_i.esc_n |=> esc_req_o)
  // correct diff encoding
  `ASSERT(DiffEncCheck_A, esc_tx_i.esc_p ^ esc_tx_i.esc_n |=> esc_rx_o.resp_p ^ esc_rx_o.resp_n)
  // disable in case of signal integrity issue
  `ASSERT(PingRespCheck_A, state_q == Idle ##1 $rose(esc_tx_i.esc_p) ##1 $fell(esc_tx_i.esc_p) |->
      $rose(esc_rx_o.resp_p) ##1 $fell(esc_rx_o.resp_p),
      clk_i, !rst_ni || (esc_tx_i.esc_p == esc_tx_i.esc_n))
  // escalation response needs to continuously toggle
  `ASSERT(EscRespCheck_A, ##1 esc_tx_i.esc_p && $past(esc_tx_i.esc_p) &&
      (esc_tx_i.esc_p ^ esc_tx_i.esc_n) && $past(esc_tx_i.esc_p ^ esc_tx_i.esc_n)
      |=> esc_rx_o.resp_p != $past(esc_rx_o.resp_p))
  // detect escalation pulse
  `ASSERT(EscEnCheck_A,
          esc_tx_i.esc_p && (esc_tx_i.esc_p ^ esc_tx_i.esc_n) && state_q != SigInt
      ##1 esc_tx_i.esc_p && (esc_tx_i.esc_p ^ esc_tx_i.esc_n) |-> esc_req_o)
  // make sure the counter does not wrap around
  `ASSERT(EscCntWrap_A, &timeout_cnt |=> timeout_cnt != 0)
  // if the counter expires, escalation should be asserted
  `ASSERT(EscCntEsc_A, &timeout_cnt |-> esc_req_o)

endmodule : prim_esc_receiver
