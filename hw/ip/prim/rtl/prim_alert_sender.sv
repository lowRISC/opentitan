// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The alert sender primitive module differentially encodes and transmits an
// alert signal to the prim_alert_receiver module. An alert will be signalled
// by a full handshake on alert_p/n and ack_p/n. The alert_req_i signal may
// be continuously asserted, in which case the alert signalling handshake
// will be repeatedly initiated.
//
// The alert_req_i signal may also be used as part of req/ack. The parent module
// can keep alert_req_i asserted until it has been ack'd (transferred to the alert
// receiver).  The parent module is not required to use this.
//
// In case the alert sender parameter IsFatal is set to 1, an incoming alert
// alert_req_i is latched in a local register until the next reset, causing the
// alert sender to behave as if alert_req_i were continously asserted.
// The alert_state_o output reflects the state of this internal latching register.
//
// The alert sender also exposes an alert test input, which can be used to trigger
// single alert handshakes. This input behaves exactly the same way as the
// alert_req_i input with IsFatal set to 0. Test alerts do not cause alert_ack_o
// to be asserted, nor are they latched until reset (regardless of the value of the
// IsFatal parameter).
//
// Further, this module supports in-band ping testing, which means that a level
// change on the ping_p/n diff pair will result in a full-handshake response
// on alert_p/n and ack_p/n.
//
// The protocol works in both asynchronous and synchronous cases. In the
// asynchronous case, the parameter AsyncOn must be set to 1'b1 in order to
// instantiate additional synchronization logic. Further, it must be ensured
// that the timing skew between all diff pairs is smaller than the shortest
// clock period of the involved clocks.
//
// Incorrectly encoded diff inputs can be detected and will be signalled
// to the receiver by placing an inconsistent diff value on the differential
// output (and continuously toggling it).
//
// See also: prim_alert_receiver, prim_diff_decode, alert_handler

`include "prim_assert.sv"

module prim_alert_sender
  import prim_alert_pkg::*;
#(
  // enables additional synchronization logic
  parameter bit AsyncOn = 1'b1,
  // alert sender will latch the incoming alert event permanently and
  // keep on sending alert events until the next reset.
  parameter bit IsFatal = 1'b0
) (
  input             clk_i,
  input             rst_ni,
  // alert test trigger (this will never be latched, even if IsFatal == 1)
  input             alert_test_i,
  // native alert from the peripheral
  input             alert_req_i,
  output logic      alert_ack_o,
  // state of the alert latching register
  output logic      alert_state_o,
  // ping input diff pair and ack diff pair
  input alert_rx_t  alert_rx_i,
  // alert output diff pair
  output alert_tx_t alert_tx_o
);


  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////
  logic ping_sigint, ping_event, ping_n, ping_p;

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_buf #(
    .Width(2)
  ) u_prim_buf_ping (
    .in_i({alert_rx_i.ping_n,
           alert_rx_i.ping_p}),
    .out_o({ping_n,
            ping_p})
  );

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) u_decode_ping (
    .clk_i,
    .rst_ni,
    .diff_pi  ( ping_p      ),
    .diff_ni  ( ping_n      ),
    .level_o  (             ),
    .rise_o   (             ),
    .fall_o   (             ),
    .event_o  ( ping_event  ),
    .sigint_o ( ping_sigint )
  );

  logic ack_sigint, ack_level, ack_n, ack_p;

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_buf #(
    .Width(2)
  ) u_prim_buf_ack (
    .in_i({alert_rx_i.ack_n,
           alert_rx_i.ack_p}),
    .out_o({ack_n,
            ack_p})
  );

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) u_decode_ack (
    .clk_i,
    .rst_ni,
    .diff_pi  ( ack_p      ),
    .diff_ni  ( ack_n      ),
    .level_o  ( ack_level  ),
    .rise_o   (            ),
    .fall_o   (            ),
    .event_o  (            ),
    .sigint_o ( ack_sigint )
  );


  ///////////////////////////////////////////////////
  // main protocol FSM that drives the diff output //
  ///////////////////////////////////////////////////
  typedef enum logic [2:0] {
    Idle,
    AlertHsPhase1,
    AlertHsPhase2,
    PingHsPhase1,
    PingHsPhase2,
    Pause0,
    Pause1
    } state_e;
  state_e state_d, state_q;
  logic alert_pq, alert_nq, alert_pd, alert_nd;
  logic sigint_detected;

  assign sigint_detected = ack_sigint | ping_sigint;


  // diff pair output
  assign alert_tx_o.alert_p = alert_pq;
  assign alert_tx_o.alert_n = alert_nq;

  // alert and ping set regs
  logic alert_set_d, alert_set_q, alert_clr;
  logic alert_test_set_d, alert_test_set_q;
  logic ping_set_d, ping_set_q, ping_clr;
  logic alert_req_trigger, alert_test_trigger, ping_trigger;

  // if handshake is ongoing, capture additional alert requests.
  logic alert_req;
  prim_sec_anchor_buf #(
    .Width(1)
  ) u_prim_buf_in_req (
    .in_i(alert_req_i),
    .out_o(alert_req)
  );

  assign alert_req_trigger = alert_req | alert_set_q;
  if (IsFatal) begin : gen_fatal
    assign alert_set_d = alert_req_trigger;
  end else begin : gen_recov
    assign alert_set_d = (alert_clr) ? 1'b0 : alert_req_trigger;
  end

  // the alert test request is always cleared.
  assign alert_test_trigger = alert_test_i | alert_test_set_q;
  assign alert_test_set_d = (alert_clr) ? 1'b0 : alert_test_trigger;

  logic alert_trigger;
  assign alert_trigger = alert_req_trigger | alert_test_trigger;

  assign ping_trigger = ping_set_q | ping_event;
  assign ping_set_d  = (ping_clr) ? 1'b0 : ping_trigger;


  // alert event acknowledge and state (not affected by alert_test_i)
  assign alert_ack_o = alert_clr & alert_set_q;
  assign alert_state_o = alert_set_q;

  // this FSM performs a full four phase handshake upon a ping or alert trigger.
  // note that the latency of the alert_p/n diff pair is at least one cycle
  // until it enters the receiver FSM. the same holds for the ack_* diff pair
  // input. in case a signal integrity issue is detected, the FSM bails out,
  // sets the alert_p/n diff pair to the same value and toggles it in order to
  // signal that condition over to the receiver.
  always_comb begin : p_fsm
    // default
    state_d   = state_q;
    alert_pd  = 1'b0;
    alert_nd  = 1'b1;
    ping_clr  = 1'b0;
    alert_clr = 1'b0;

    unique case (state_q)
      Idle: begin
        // alert always takes precedence
        if (alert_trigger || ping_trigger) begin
          state_d = (alert_trigger) ? AlertHsPhase1 : PingHsPhase1;
          alert_pd = 1'b1;
          alert_nd = 1'b0;
        end
      end
      // waiting for ack from receiver
      AlertHsPhase1: begin
        if (ack_level) begin
          state_d  = AlertHsPhase2;
        end else begin
          alert_pd = 1'b1;
          alert_nd = 1'b0;
        end
      end
      // wait for deassertion of ack
      AlertHsPhase2: begin
        if (!ack_level) begin
          state_d = Pause0;
          alert_clr = 1'b1;
        end
      end
      // waiting for ack from receiver
      PingHsPhase1: begin
        if (ack_level) begin
          state_d  = PingHsPhase2;
        end else begin
          alert_pd = 1'b1;
          alert_nd = 1'b0;
        end
      end
      // wait for deassertion of ack
      PingHsPhase2: begin
        if (!ack_level) begin
          ping_clr = 1'b1;
          state_d = Pause0;
        end
      end
      // pause cycles between back-to-back handshakes
      Pause0: begin
        state_d = Pause1;
      end
      // clear and ack alert request if it was set
      Pause1: begin
        state_d = Idle;
      end
      // catch parasitic states
      default : state_d = Idle;
    endcase

    // we have a signal integrity issue at one of the incoming diff pairs. this condition is
    // signalled by setting the output diffpair to zero. If the sigint has disappeared, we clear
    // the ping request state of this sender and go back to idle.
    if (sigint_detected) begin
      state_d   = Idle;
      alert_pd  = 1'b0;
      alert_nd  = 1'b0;
      ping_clr  = 1'b1;
      alert_clr = 1'b0;
    end
  end

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_flop #(
    .Width     (2),
    .ResetValue(2'b10)
  ) u_prim_flop_alert (
    .clk_i,
    .rst_ni,
    .d_i({alert_nd, alert_pd}),
    .q_o({alert_nq, alert_pq})
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
    if (!rst_ni) begin
      state_q          <= Idle;
      alert_set_q      <= 1'b0;
      alert_test_set_q <= 1'b0;
      ping_set_q       <= 1'b0;
    end else begin
      state_q          <= state_d;
      alert_set_q      <= alert_set_d;
      alert_test_set_q <= alert_test_set_d;
      ping_set_q       <= ping_set_d;
    end
  end


  ////////////////
  // assertions //
  ////////////////

// however, since we use sequence constructs below, we need to wrap the entire block again.
// typically, the ASSERT macros already contain this INC_ASSERT macro.
`ifdef INC_ASSERT
  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(AlertPKnownO_A, alert_tx_o)

  if (AsyncOn) begin : gen_async_assert
    sequence PingSigInt_S;
      alert_rx_i.ping_p == alert_rx_i.ping_n [*2];
    endsequence
    sequence AckSigInt_S;
      alert_rx_i.ping_p == alert_rx_i.ping_n [*2];
    endsequence

  `ifndef FPV_ALERT_NO_SIGINT_ERR
    // check propagation of sigint issues to output within three cycles
    // shift sequence to the right to avoid reset effects.
    `ASSERT(SigIntPing_A, ##1 PingSigInt_S |->
        ##3 alert_tx_o.alert_p == alert_tx_o.alert_n)
    `ASSERT(SigIntAck_A, ##1 AckSigInt_S |->
        ##3 alert_tx_o.alert_p == alert_tx_o.alert_n)
  `endif

    // Test in-band FSM reset request (via signal integrity error)
    `ASSERT(InBandInitFsm_A, PingSigInt_S or AckSigInt_S |-> ##3 state_q == Idle)
    `ASSERT(InBandInitPing_A, PingSigInt_S or AckSigInt_S |-> ##3 !ping_set_q)
    // output must be driven diff unless sigint issue detected
    `ASSERT(DiffEncoding_A, (alert_rx_i.ack_p ^ alert_rx_i.ack_n) &&
        (alert_rx_i.ping_p ^ alert_rx_i.ping_n) |->
        ##[3:4] alert_tx_o.alert_p ^ alert_tx_o.alert_n)

    // handshakes can take indefinite time if blocked due to sigint on outgoing
    // lines (which is not visible here). thus, we only check whether the
    // handshake is correctly initiated and defer the full handshake checking to the testbench.
    // TODO: add the staggered cases as well
    `ASSERT(PingHs_A, ##1 $changed(alert_rx_i.ping_p) &&
        (alert_rx_i.ping_p ^ alert_rx_i.ping_n) ##2 state_q == Idle |=>
        $rose(alert_tx_o.alert_p), clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))
  end else begin : gen_sync_assert
    sequence PingSigInt_S;
      alert_rx_i.ping_p == alert_rx_i.ping_n;
    endsequence
    sequence AckSigInt_S;
      alert_rx_i.ping_p == alert_rx_i.ping_n;
    endsequence

  `ifndef FPV_ALERT_NO_SIGINT_ERR
    // check propagation of sigint issues to output within one cycle
    `ASSERT(SigIntPing_A, PingSigInt_S |=>
        alert_tx_o.alert_p == alert_tx_o.alert_n)
    `ASSERT(SigIntAck_A,  AckSigInt_S |=>
        alert_tx_o.alert_p == alert_tx_o.alert_n)
  `endif

    // Test in-band FSM reset request (via signal integrity error)
    `ASSERT(InBandInitFsm_A, PingSigInt_S or AckSigInt_S |=> state_q == Idle)
    `ASSERT(InBandInitPing_A, PingSigInt_S or AckSigInt_S |=> !ping_set_q)
    // output must be driven diff unless sigint issue detected
    `ASSERT(DiffEncoding_A, (alert_rx_i.ack_p ^ alert_rx_i.ack_n) &&
        (alert_rx_i.ping_p ^ alert_rx_i.ping_n) |=> alert_tx_o.alert_p ^ alert_tx_o.alert_n)
    // handshakes can take indefinite time if blocked due to sigint on outgoing
    // lines (which is not visible here). thus, we only check whether the handshake
    // is correctly initiated and defer the full handshake checking to the testbench.
    `ASSERT(PingHs_A, ##1 $changed(alert_rx_i.ping_p) && state_q == Idle |=>
        $rose(alert_tx_o.alert_p), clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))
  end

  // Test the alert state output.
  `ASSERT(AlertState0_A, alert_set_q === alert_state_o)

  if (IsFatal) begin : gen_fatal_assert
    `ASSERT(AlertState1_A, alert_req_i |=> alert_state_o)
    `ASSERT(AlertState2_A, alert_state_o |=> $stable(alert_state_o))
    `ASSERT(AlertState3_A, alert_ack_o |=> alert_state_o)
  end else begin : gen_recov_assert
    `ASSERT(AlertState1_A, alert_req_i && !alert_clr |=> alert_state_o)
    `ASSERT(AlertState2_A, alert_req_i && alert_ack_o |=> !alert_state_o)
  end

  // The alert test input should not set the alert state register.
  `ASSERT(AlertTest1_A, alert_test_i && !alert_req_i && !alert_state_o |=> $stable(alert_state_o))

  // if alert_req_i is true, handshakes should be continuously repeated
  `ASSERT(AlertHs_A, alert_req_i && state_q == Idle |=> $rose(alert_tx_o.alert_p),
      clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))

  // if alert_test_i is true, handshakes should be continuously repeated
  `ASSERT(AlertTestHs_A, alert_test_i && state_q == Idle |=> $rose(alert_tx_o.alert_p),
      clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))
`endif

`ifdef FPV_ALERT_NO_SIGINT_ERR
  // Assumptions for FPV security countermeasures to ensure the alert protocol functions collectly.
  `ASSUME_FPV(AckPFollowsAlertP_S, alert_rx_i.ack_p == $past(alert_tx_o.alert_p))
  `ASSUME_FPV(AckNFollowsAlertN_S, alert_rx_i.ack_n == $past(alert_tx_o.alert_n))
  `ASSUME_FPV(TriggerAlertInit_S, $stable(rst_ni) == 0 |=> alert_rx_i.ping_p == alert_rx_i.ping_n)
  `ASSUME_FPV(PingDiffPair_S, ##2 alert_rx_i.ping_p != alert_rx_i.ping_n)
`endif
endmodule : prim_alert_sender
