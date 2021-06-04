// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module differentially encodes an escalation enable pulse
// of arbitrary width.
//
// The module supports in-band ping testing of the escalation
// wires. This is accomplished by sending out a single, differentially
// encoded pulse on esc_p/n which will be interpreted as a ping
// request by the escalation receiver. Note that ping_req_i shall
// be held high until either ping_ok_o or integ_fail_o is asserted.
//
// Native escalation enable pulses are differentiated from ping
// requests by making sure that these pulses are always longer than 1 cycle.
//
// If there is a differential encoding error, integ_fail_o
// will be asserted.
//
// See also: prim_esc_receiver, prim_diff_decode, alert_handler

`include "prim_assert.sv"

module prim_esc_sender
  import prim_esc_pkg::*;
(
  input           clk_i,
  input           rst_ni,
  // this triggers a ping test. keep asserted until ping_ok_o is pulsed high.
  input           ping_req_i,
  output logic    ping_ok_o,
  // asserted if signal integrity issue detected
  output logic    integ_fail_o,
  // escalation request signal
  input           esc_req_i,
  // escalation / ping response
  input esc_rx_t  esc_rx_i,
  // escalation output diff pair
  output esc_tx_t esc_tx_o
);

  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////

  logic resp, resp_n, resp_p, sigint_detected;

  // This prevents further tool optimizations of the differential signal.
  prim_buf #(
    .Width(2)
  ) u_prim_buf_resp (
    .in_i({esc_rx_i.resp_n,
           esc_rx_i.resp_p}),
    .out_o({resp_n,
            resp_p})
  );

  prim_diff_decode #(
    .AsyncOn(1'b0)
  ) u_decode_resp (
    .clk_i,
    .rst_ni,
    .diff_pi  ( resp_p          ),
    .diff_ni  ( resp_n          ),
    .level_o  ( resp            ),
    .rise_o   (                 ),
    .fall_o   (                 ),
    .event_o  (                 ),
    .sigint_o ( sigint_detected )
  );

  //////////////
  // TX Logic //
  //////////////

  logic ping_req_d, ping_req_q;
  logic esc_req_d, esc_req_q, esc_req_q1;

  assign ping_req_d = ping_req_i;
  assign esc_req_d  = esc_req_i;

  // ping enable is 1 cycle pulse
  // escalation pulse is always longer than 2 cycles
  logic esc_p;
  assign esc_p = esc_req_i | esc_req_q | (ping_req_d & ~ping_req_q);

  // This prevents further tool optimizations of the differential signal.
  prim_buf #(
    .Width(2)
  ) u_prim_buf_esc (
    .in_i({~esc_p,
           esc_p}),
    .out_o({esc_tx_o.esc_n,
            esc_tx_o.esc_p})
  );

  //////////////
  // RX Logic //
  //////////////

  typedef enum logic [2:0] {Idle, CheckEscRespLo, CheckEscRespHi,
    CheckPingResp0, CheckPingResp1, CheckPingResp2, CheckPingResp3} fsm_e;

  fsm_e state_d, state_q;

  always_comb begin : p_fsm
    // default
    state_d      = state_q;
    ping_ok_o    = 1'b0;
    integ_fail_o = sigint_detected;

    unique case (state_q)
      // wait for ping or escalation enable
      Idle: begin
        if (esc_req_i) begin
          state_d = CheckEscRespHi;
        end else if (ping_req_i) begin
          state_d = CheckPingResp0;
        end
        // any assertion of the response signal
        // signal here will trigger a sigint error
        if (resp) begin
          integ_fail_o = 1'b1;
        end
      end
      // check whether response is 0
      CheckEscRespLo: begin
        state_d      = CheckEscRespHi;
        if (!esc_tx_o.esc_p || resp) begin
          state_d = Idle;
          integ_fail_o = sigint_detected | resp;
        end
      end
      // check whether response is 1
      CheckEscRespHi: begin
        state_d = CheckEscRespLo;
        if (!esc_tx_o.esc_p || !resp) begin
          state_d = Idle;
          integ_fail_o = sigint_detected | ~resp;
        end
      end
      // start of ping response sequence
      // we expect the sequence "1010"
      CheckPingResp0: begin
        state_d = CheckPingResp1;
        // abort sequence immediately if escalation is signalled,
        // jump to escalation response checking (lo state)
        if (esc_req_i) begin
          state_d = CheckEscRespLo;
        // abort if response is wrong
        end else if (!resp) begin
          state_d = Idle;
          integ_fail_o = 1'b1;
        end
      end
      CheckPingResp1: begin
        state_d = CheckPingResp2;
        // abort sequence immediately if escalation is signalled,
        // jump to escalation response checking (hi state)
        if (esc_req_i) begin
          state_d = CheckEscRespHi;
        // abort if response is wrong
        end else if (resp) begin
          state_d = Idle;
          integ_fail_o = 1'b1;
        end
      end
      CheckPingResp2: begin
        state_d = CheckPingResp3;
        // abort sequence immediately if escalation is signalled,
        // jump to escalation response checking (lo state)
        if (esc_req_i) begin
          state_d = CheckEscRespLo;
        // abort if response is wrong
        end else if (!resp) begin
          state_d = Idle;
          integ_fail_o = 1'b1;
        end
      end
      CheckPingResp3: begin
        state_d = Idle;
        // abort sequence immediately if escalation is signalled,
        // jump to escalation response checking (hi state)
        if (esc_req_i) begin
          state_d = CheckEscRespHi;
        // abort if response is wrong
        end else if (resp) begin
          integ_fail_o = 1'b1;
        end else begin
          ping_ok_o = ping_req_i;
        end
      end
      default : state_d = Idle;
    endcase

    // a sigint error will reset the state machine
    // and have it pause for two cycles to let the
    // receiver recover
    if (sigint_detected) begin
      ping_ok_o = 1'b0;
      state_d = Idle;
    end

    // escalation takes precedence,
    // immediately return ok in that case
    if ((esc_req_i || esc_req_q || esc_req_q1) && ping_req_i) begin
      ping_ok_o = 1'b1;
    end
  end

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q   <= Idle;
      esc_req_q  <= 1'b0;
      esc_req_q1 <= 1'b0;
      ping_req_q <= 1'b0;
    end else begin
      state_q   <= state_d;
      esc_req_q  <= esc_req_d;
      esc_req_q1 <= esc_req_q;
      ping_req_q <= ping_req_d;
    end
  end

  ////////////////
  // assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(PingOkKnownO_A, ping_ok_o)
  `ASSERT_KNOWN(IntegFailKnownO_A, integ_fail_o)
  `ASSERT_KNOWN(EscPKnownO_A, esc_tx_o)

  // diff encoding of output
  `ASSERT(DiffEncCheck_A, esc_tx_o.esc_p ^ esc_tx_o.esc_n)
  // signal integrity check propagation
  `ASSERT(SigIntCheck0_A, esc_rx_i.resp_p == esc_rx_i.resp_n  |-> integ_fail_o)
  // this happens in case we did not get a correct escalation response
  `ASSERT(SigIntCheck1_A, ##1 $rose(esc_req_i) &&
      state_q inside {Idle, CheckPingResp1, CheckPingResp3} ##1 !esc_rx_i.resp_p |->
      integ_fail_o, clk_i, !rst_ni || (esc_rx_i.resp_p == esc_rx_i.resp_n) ||
      (state_q == Idle && resp))
  `ASSERT(SigIntCheck2_A, ##1 $rose(esc_req_i) &&
      state_q inside {CheckPingResp0, CheckPingResp2} ##1 esc_rx_i.resp_p |->
      integ_fail_o, clk_i, !rst_ni || (esc_rx_i.resp_p == esc_rx_i.resp_n) ||
      (state_q == Idle && resp))
  // unexpected response
  `ASSERT(SigIntCheck3_A, state_q == Idle && resp |-> integ_fail_o)
  // signal_int_backward_check
  `ASSERT(SigIntBackCheck_A, integ_fail_o |-> (esc_rx_i.resp_p == esc_rx_i.resp_n) ||
      (esc_rx_i.resp_p && !(state_q == CheckEscRespHi)) ||
      (!esc_rx_i.resp_p && !(state_q == CheckEscRespLo)))
  // state machine CheckEscRespLo and Hi as they are ideal resp signals
  `ASSERT(StateEscRespHiCheck_A, state_q == CheckEscRespLo && esc_tx_o.esc_p && !integ_fail_o |=>
      state_q == CheckEscRespHi)
  `ASSERT(StateEscRespLoCheck_A, state_q == CheckEscRespHi && esc_tx_o.esc_p && !integ_fail_o |=>
      state_q == CheckEscRespLo)
  `ASSERT(StateEscRespHiBackCheck_A, state_q == CheckEscRespHi |-> $past(esc_tx_o.esc_p))
  `ASSERT(StateEscRespLoBackCheck_A, state_q == CheckEscRespLo |-> $past(esc_tx_o.esc_p))
  // check that escalation signal is at least 2 cycles high
  `ASSERT(EscCheck_A, esc_req_i |-> esc_tx_o.esc_p [*2] )
  // escalation / ping collision
  `ASSERT(EscPingCheck_A, esc_req_i && ping_req_i |-> ping_ok_o)
  // check that ping request results in only a single cycle pulse
  `ASSERT(PingCheck_A, ##1 $rose(ping_req_i) |-> esc_tx_o.esc_p ##1 !esc_tx_o.esc_p , clk_i,
      !rst_ni || esc_req_i || integ_fail_o)

endmodule : prim_esc_sender
