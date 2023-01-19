// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The alert receiver primitive decodes alerts that have been differentially
// encoded and transmitted via a handshake protocol on alert_p/n and
// ack_p/n. In case an alert handshake is initiated, the output alert_o will
// immediately be asserted (even before completion of the handshake).
//
// In case the differential input is not correctly encoded, this module will
// raise an error by asserting integ_fail_o.
//
// Further, the module supports ping testing of the alert diff pair. In order to
// initiate a ping test, ping_req_i shall be set to 1'b1 until ping_ok_o is
// asserted for one cycle. The signal may be de-asserted (e.g. after a long)
// timeout period. However note that all ping responses that come in after
// deasserting ping_req_i will be treated as native alerts.
//
// The protocol works in both asynchronous and synchronous cases. In the
// asynchronous case, the parameter AsyncOn must be set to 1'b1 in order to
// instantiate additional synchronization logic. Further, it must be ensured
// that the timing skew between all diff pairs is smaller than the shortest
// clock period of the involved clocks.
//
// Note that in case of synchronous operation, alerts on the diffpair are
// decoded combinationally and forwarded on alert_o within the same cycle.
//
// See also: prim_alert_sender, prim_diff_decode, alert_handler

`include "prim_assert.sv"

module prim_alert_receiver
  import prim_alert_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  // enables additional synchronization logic
  parameter bit AsyncOn = 1'b0
) (
  input             clk_i,
  input             rst_ni,
  // if set to lc_ctrl_pkg::On, this triggers the in-band alert channel
  // reset, which resets both the sender and receiver FSMs into IDLE.
  input mubi4_t     init_trig_i,
  // this triggers a ping test. keep asserted
  // until ping_ok_o is asserted.
  input             ping_req_i,
  output logic      ping_ok_o,
  // asserted if signal integrity issue detected
  output logic      integ_fail_o,
  // alert output (pulsed high) if a handshake is initiated
  // on alert_p/n and no ping request is outstanding
  output logic      alert_o,
  // ping input diff pair and ack diff pair
  output alert_rx_t alert_rx_o,
  // alert output diff pair
  input alert_tx_t  alert_tx_i
);

  import prim_mubi_pkg::mubi4_test_true_strict;

  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////
  logic alert_level, alert_sigint, alert_p, alert_n;

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_buf #(
    .Width(2)
  ) u_prim_buf_in (
    .in_i({alert_tx_i.alert_n,
           alert_tx_i.alert_p}),
    .out_o({alert_n,
            alert_p})
  );

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) u_decode_alert (
    .clk_i,
    .rst_ni,
    .diff_pi  ( alert_p            ),
    .diff_ni  ( alert_n            ),
    .level_o  ( alert_level        ),
    .rise_o   (                    ),
    .fall_o   (                    ),
    .event_o  (                    ),
    .sigint_o ( alert_sigint       )
  );

  /////////////////////////////////////////////////////
  //  main protocol FSM that drives the diff outputs //
  /////////////////////////////////////////////////////
  typedef enum logic [2:0] {Idle, HsAckWait, Pause0, Pause1, InitReq, InitAckWait} state_e;
  state_e state_d, state_q;
  logic ping_rise;
  logic ping_tog_pd, ping_tog_pq, ping_tog_dn, ping_tog_nq;
  logic ack_pd, ack_pq, ack_dn, ack_nq;
  logic ping_req_d, ping_req_q;
  logic ping_pending_d, ping_pending_q;
  logic send_init;
  logic send_ping;

  // signal ping request upon positive transition on ping_req_i
  // signalling is performed by a level change event on the diff output
  assign ping_req_d  = ping_req_i;
  assign ping_rise   = ping_req_d && !ping_req_q;
  assign ping_tog_pd = (send_init) ? 1'b0         :
                       (send_ping) ? ~ping_tog_pq : ping_tog_pq;

  // in-band reset is performed by sending out an integrity error on purpose.
  assign ack_dn      = (send_init) ? ack_pd : ~ack_pd;
  assign ping_tog_dn = ~ping_tog_pd;

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_flop #(
    .Width     (2),
    .ResetValue(2'b10)
  ) u_prim_generic_flop_ack (
    .clk_i,
    .rst_ni,
    .d_i({ack_dn,
          ack_pd}),
    .q_o({ack_nq,
          ack_pq})
  );

  prim_sec_anchor_flop #(
    .Width     (2),
    .ResetValue(2'b10)
  ) u_prim_generic_flop_ping (
    .clk_i,
    .rst_ni,
    .d_i({ping_tog_dn,
          ping_tog_pd}),
    .q_o({ping_tog_nq,
          ping_tog_pq})
  );

  // the ping pending signal is used in the FSM to distinguish whether the
  // incoming handshake shall be treated as an alert or a ping response.
  // it is important that this is only set on a rising ping_en level change, since
  // otherwise the ping enable signal could be abused to "mask" all native alerts
  // as ping responses by constantly tying it to 1.
  assign ping_pending_d = ping_rise | ((~ping_ok_o) & ping_req_i & ping_pending_q);

  // diff pair outputs
  assign alert_rx_o.ack_p = ack_pq;
  assign alert_rx_o.ack_n = ack_nq;

  assign alert_rx_o.ping_p = ping_tog_pq;
  assign alert_rx_o.ping_n = ping_tog_nq;

  // this FSM receives the four phase handshakes from the alert receiver
  // note that the latency of the alert_p/n input diff pair is at least one
  // cycle until it enters the receiver FSM. the same holds for the ack_* diff
  // pair outputs.
  always_comb begin : p_fsm
    // default
    state_d      = state_q;
    ack_pd       = 1'b0;
    ping_ok_o    = 1'b0;
    integ_fail_o = 1'b0;
    alert_o      = 1'b0;
    send_init    = 1'b0;
    // by default, a ping request leads to a toogle on the differential ping pair
    send_ping    = ping_rise;

    unique case (state_q)
      Idle: begin
        // wait for handshake to be initiated
        if (alert_level) begin
          state_d = HsAckWait;
          ack_pd  = 1'b1;
          // signal either an alert or ping received on the output
          if (ping_pending_q) begin
            ping_ok_o = 1'b1;
          end else begin
            alert_o   = 1'b1;
          end
        end
      end
      // waiting for deassertion of alert to complete HS
      HsAckWait: begin
        if (!alert_level) begin
          state_d  = Pause0;
        end else begin
          ack_pd = 1'b1;
        end
      end
      // pause cycles between back-to-back handshakes
      Pause0: state_d = Pause1;
      Pause1: state_d = Idle;
      // this state is only reached if an in-band reset is
      // requested via the low-power logic.
      InitReq: begin
        // we deliberately place a sigint error on the ack and ping lines in this case.
        send_init = 1'b1;
        // suppress any toggles on the ping line while we are in the init phase.
        send_ping = 1'b0;
        // As long as init req is asserted, we remain in this state and acknowledge all incoming
        // ping requests. As soon as the init request is dropped however, ping requests are not
        // acked anymore such that the ping mechanism can also flag alert channels that got stuck
        // in the initialization sequence.
        if (mubi4_test_true_strict(init_trig_i)) begin
          ping_ok_o = ping_pending_q;
        // the sender will respond to the sigint error above with a sigint error on the alert lines.
        // hence we treat the alert_sigint like an acknowledgement in this case.
        end else if (alert_sigint) begin
          state_d = InitAckWait;
        end
      end
      // We get here if the sender has responded with alert_sigint, and init_trig_i==lc_ctrl_pkg::On
      // has been deasserted. At this point, we need to wait for the alert_sigint to drop again
      // before resuming normal operation.
      InitAckWait: begin
        // suppress any toggles on the ping line while we are in the init phase.
        send_ping = 1'b0;
        if (!alert_sigint) begin
          state_d = Pause0;
          // If we get a ping request in this cycle, or if we realize that there is an unhandled
          // ping request that came in during initialization (but after init_trig_i has been
          // deasserted), we signal this to the alert sender by toggling the request line.
          send_ping = ping_rise || ping_pending_q;
        end
      end
      default: state_d = Idle;
    endcase

    // once the initialization sequence has been triggered,
    // overrides are not allowed anymore until the initialization has been completed.
    if (!(state_q inside {InitReq, InitAckWait})) begin
      // in this case, abort and jump into the initialization sequence
      if (mubi4_test_true_strict(init_trig_i)) begin
        state_d      = InitReq;
        ack_pd       = 1'b0;
        ping_ok_o    = 1'b0;
        integ_fail_o = 1'b0;
        alert_o      = 1'b0;
        send_init    = 1'b1;
      // if we're not busy with an init request, we clamp down all outputs
      // and indicate an integrity failure.
      end else if (alert_sigint) begin
        state_d      = Idle;
        ack_pd       = 1'b0;
        ping_ok_o    = 1'b0;
        integ_fail_o = 1'b1;
        alert_o      = 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
    if (!rst_ni) begin
      // Reset into the init request so that an alert handler reset implicitly
      // triggers an in-band reset of all alert channels.
      state_q        <= InitReq;
      ping_req_q     <= 1'b0;
      ping_pending_q <= 1'b0;
    end else begin
      state_q        <= state_d;
      ping_req_q     <= ping_req_d;
      ping_pending_q <= ping_pending_d;
    end
  end


  ////////////////
  // assertions //
  ////////////////

`ifdef INC_ASSERT
  import prim_mubi_pkg::mubi4_test_false_loose;
`endif

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(PingOkKnownO_A, ping_ok_o)
  `ASSERT_KNOWN(IntegFailKnownO_A, integ_fail_o)
  `ASSERT_KNOWN(AlertKnownO_A, alert_o)
  `ASSERT_KNOWN(PingPKnownO_A, alert_rx_o)

  // check encoding of outgoing diffpairs. note that during init, the outgoing diffpairs are
  // supposed to be incorrectly encoded on purpose.
  // shift sequence two cycles to the right to avoid reset effects.
  `ASSERT(PingDiffOk_A, alert_rx_o.ping_p ^ alert_rx_o.ping_n)
  `ASSERT(AckDiffOk_A, ##2 $past(send_init) ^ alert_rx_o.ack_p ^ alert_rx_o.ack_n)
  `ASSERT(InitReq_A, mubi4_test_true_strict(init_trig_i) &&
          !(state_q inside {InitReq, InitAckWait}) |=> send_init)

  // ping request at input -> need to see encoded ping request
  `ASSERT(PingRequest0_A, ##1 $rose(ping_req_i) && !state_q inside {InitReq, InitAckWait}
      |=> $changed(alert_rx_o.ping_p))
  // ping response implies it has been requested
  `ASSERT(PingResponse0_A, ping_ok_o |-> ping_pending_q)
  // correctly latch ping request
  `ASSERT(PingPending_A, ##1 $rose(ping_req_i) |=> ping_pending_q)

  if (AsyncOn) begin : gen_async_assert
    // signal integrity check propagation
    `ASSERT(SigInt_A,
        alert_tx_i.alert_p == alert_tx_i.alert_n [*2] ##2
        !(state_q inside {InitReq, InitAckWait}) &&
        mubi4_test_false_loose(init_trig_i)
        |->
        integ_fail_o)
    // TODO: need to add skewed cases as well, the assertions below assume no skew at the moment
    // ping response
    `ASSERT(PingResponse1_A,
        ##1 $rose(alert_tx_i.alert_p) &&
        (alert_tx_i.alert_p ^ alert_tx_i.alert_n) ##2
        state_q == Idle && ping_pending_q
        |->
        ping_ok_o,
        clk_i, !rst_ni || integ_fail_o || mubi4_test_true_strict(init_trig_i))
    // alert
    `ASSERT(Alert_A,
        ##1 $rose(alert_tx_i.alert_p) &&
        (alert_tx_i.alert_p ^ alert_tx_i.alert_n) ##2
        state_q == Idle &&
        !ping_pending_q
        |->
        ##[0:1] alert_o,
        clk_i, !rst_ni || integ_fail_o || mubi4_test_true_strict(init_trig_i))
  end else begin : gen_sync_assert
    // signal integrity check propagation
    `ASSERT(SigInt_A,
        alert_tx_i.alert_p == alert_tx_i.alert_n &&
        !(state_q inside {InitReq, InitAckWait}) &&
        mubi4_test_false_loose(init_trig_i)
        |->
        integ_fail_o)
    // ping response
    `ASSERT(PingResponse1_A,
        ##1 $rose(alert_tx_i.alert_p) &&
        state_q == Idle &&
        ping_pending_q
        |->
        ping_ok_o,
        clk_i, !rst_ni || integ_fail_o || mubi4_test_true_strict(init_trig_i))
    // alert
    `ASSERT(Alert_A,
        ##1 $rose(alert_tx_i.alert_p) &&
        state_q == Idle &&
        !ping_pending_q
        |->
        alert_o,
        clk_i, !rst_ni || integ_fail_o || mubi4_test_true_strict(init_trig_i))
  end

  // check in-band init request is always accepted
  `ASSERT(InBandInitRequest_A,
      mubi4_test_true_strict(init_trig_i) &&
      state_q != InitAckWait
      |=>
      state_q == InitReq)
  // check in-band init sequence moves FSM into IDLE state
  `ASSERT(InBandInitSequence_A,
      (state_q == InitReq &&
      mubi4_test_true_strict(init_trig_i)) ##1
      (alert_sigint &&
      mubi4_test_false_loose(init_trig_i)) [*1:$] ##1
      (!alert_sigint &&
      mubi4_test_false_loose(init_trig_i)) [*3]
      |=>
      state_q == Idle)
  // check there are no spurious alerts during init
  `ASSERT(NoSpuriousAlertsDuringInit_A,
      mubi4_test_true_strict(init_trig_i) ||
      (state_q inside {InitReq, InitAckWait})
      |->
      !alert_o)
  // check that there are no spurious ping OKs
  `ASSERT(NoSpuriousPingOksDuringInit_A,
      (mubi4_test_true_strict(init_trig_i) ||
      (state_q inside {InitReq, InitAckWait})) &&
      !ping_pending_q
      |->
      !ping_ok_o)
  // check ping request is bypassed when in init state
  `ASSERT(PingOkBypassDuringInit_A,
      $rose(ping_req_i) ##1
      state_q == InitReq &&
      mubi4_test_true_strict(init_trig_i)
      |->
      ping_ok_o)

endmodule : prim_alert_receiver
