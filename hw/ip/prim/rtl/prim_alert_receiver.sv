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
#(
  // enables additional synchronization logic
  parameter bit AsyncOn = 1'b0
) (
  input             clk_i,
  input             rst_ni,
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


  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////
  logic alert_level, alert_sigint;

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) i_decode_alert (
    .clk_i,
    .rst_ni,
    .diff_pi  ( alert_tx_i.alert_p ),
    .diff_ni  ( alert_tx_i.alert_n ),
    .level_o  ( alert_level        ),
    .rise_o   (                    ),
    .fall_o   (                    ),
    .event_o  (                    ),
    .sigint_o ( alert_sigint       )
  );

  /////////////////////////////////////////////////////
  //  main protocol FSM that drives the diff outputs //
  /////////////////////////////////////////////////////
  typedef enum logic [1:0] {Idle, HsAckWait, Pause0, Pause1} state_e;
  state_e state_d, state_q;
  logic ping_rise;
  logic ping_tog, ping_tog_dp, ping_tog_qp, ping_tog_dn, ping_tog_qn;
  logic ack, ack_dp, ack_qp, ack_dn, ack_qn;
  logic ping_req_d, ping_req_q;
  logic ping_pending_d, ping_pending_q;

  // signal ping request upon positive transition on ping_req_i
  // signalling is performed by a level change event on the diff output
  assign ping_req_d  = ping_req_i;
  assign ping_rise  = ping_req_i && !ping_req_q;
  assign ping_tog = (ping_rise) ? ~ping_tog_qp : ping_tog_qp;

  // This prevents further tool optimizations of the differential signal.
  prim_buf u_prim_buf_ack_p (
    .in_i(ack),
    .out_o(ack_dp)
  );
  prim_buf u_prim_buf_ack_n (
    .in_i(~ack),
    .out_o(ack_dn)
  );
  prim_buf u_prim_buf_ping_p (
    .in_i(ping_tog),
    .out_o(ping_tog_dp)
  );
  prim_buf u_prim_buf_ping_n (
    .in_i(~ping_tog),
    .out_o(ping_tog_dn)
  );

  // the ping pending signal is used to in the FSM to distinguish whether the
  // incoming handshake shall be treated as an alert or a ping response.
  // it is important that this is only set on a rising ping_en level change, since
  // otherwise the ping enable signal could be abused to "mask" all native alerts
  // as ping responses by constantly tying it to 1.
  assign ping_pending_d = ping_rise | ((~ping_ok_o) & ping_req_i & ping_pending_q);

  // diff pair outputs
  assign alert_rx_o.ack_p = ack_qp;
  assign alert_rx_o.ack_n = ack_qn;

  assign alert_rx_o.ping_p = ping_tog_qp;
  assign alert_rx_o.ping_n = ping_tog_qn;

  // this FSM receives the four phase handshakes from the alert receiver
  // note that the latency of the alert_p/n input diff pair is at least one
  // cycle until it enters the receiver FSM. the same holds for the ack_* diff
  // pair outputs.
  always_comb begin : p_fsm
    // default
    state_d      = state_q;
    ack          = 1'b0;
    ping_ok_o    = 1'b0;
    integ_fail_o = 1'b0;
    alert_o      = 1'b0;

    unique case (state_q)
      Idle: begin
        // wait for handshake to be initiated
        if (alert_level) begin
          state_d = HsAckWait;
          ack     = 1'b1;
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
          ack      = 1'b1;
        end
      end
      // pause cycles between back-to-back handshakes
      Pause0: state_d = Pause1;
      Pause1: state_d = Idle;
      default : ; // full case
    endcase

    // override in case of sigint
    if (alert_sigint) begin
      state_d      = Idle;
      ack          = 1'b0;
      ping_ok_o    = 1'b0;
      integ_fail_o = 1'b1;
      alert_o      = 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
    if (!rst_ni) begin
      state_q        <= Idle;
      ack_qp         <= 1'b0;
      ack_qn         <= 1'b1;
      ping_tog_qp    <= 1'b0;
      ping_tog_qn    <= 1'b1;
      ping_req_q     <= 1'b0;
      ping_pending_q <= 1'b0;
    end else begin
      state_q        <= state_d;
      ack_qp         <= ack_dp;
      ack_qn         <= ack_dn;
      ping_tog_qp    <= ping_tog_dp;
      ping_tog_qn    <= ping_tog_dn;
      ping_req_q     <= ping_req_d;
      ping_pending_q <= ping_pending_d;
    end
  end


  ////////////////
  // assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(PingOkKnownO_A, ping_ok_o)
  `ASSERT_KNOWN(IntegFailKnownO_A, integ_fail_o)
  `ASSERT_KNOWN(AlertKnownO_A, alert_o)
  `ASSERT_KNOWN(PingPKnownO_A, alert_rx_o)

  // check encoding of outgoing diffpairs
  `ASSERT(PingDiffOk_A, alert_rx_o.ping_p ^ alert_rx_o.ping_n)
  `ASSERT(AckDiffOk_A, alert_rx_o.ack_p ^ alert_rx_o.ack_n)
  // ping request at input -> need to see encoded ping request
  `ASSERT(PingRequest0_A, ##1 $rose(ping_req_i) |=> $changed(alert_rx_o.ping_p))
  // ping response implies it has been requested
  `ASSERT(PingResponse0_A, ping_ok_o |-> ping_pending_q)
  // correctly latch ping request
  `ASSERT(PingPending_A, ##1 $rose(ping_req_i) |=> ping_pending_q)

  if (AsyncOn) begin : gen_async_assert
    // signal integrity check propagation
    `ASSERT(SigInt_A, alert_tx_i.alert_p == alert_tx_i.alert_n [*2] |->
        ##2 integ_fail_o)
    // TODO: need to add skewed cases as well, the assertions below assume no skew at the moment
    // ping response
    `ASSERT(PingResponse1_A, ##1 $rose(alert_tx_i.alert_p) &&
        (alert_tx_i.alert_p ^ alert_tx_i.alert_n) ##2 state_q == Idle && ping_pending_q |->
        ping_ok_o, clk_i, !rst_ni || integ_fail_o)
    // alert
    `ASSERT(Alert_A, ##1 $rose(alert_tx_i.alert_p) && (alert_tx_i.alert_p ^ alert_tx_i.alert_n) ##2
        state_q == Idle && !ping_pending_q |-> alert_o, clk_i, !rst_ni || integ_fail_o)
  end else begin : gen_sync_assert
    // signal integrity check propagation
    `ASSERT(SigInt_A, alert_tx_i.alert_p == alert_tx_i.alert_n |-> integ_fail_o)
    // ping response
    `ASSERT(PingResponse1_A, ##1 $rose(alert_tx_i.alert_p) && state_q == Idle && ping_pending_q |->
        ping_ok_o, clk_i, !rst_ni || integ_fail_o)
    // alert
    `ASSERT(Alert_A, ##1 $rose(alert_tx_i.alert_p) && state_q == Idle && !ping_pending_q |->
        alert_o, clk_i, !rst_ni || integ_fail_o)
  end

endmodule : prim_alert_receiver
