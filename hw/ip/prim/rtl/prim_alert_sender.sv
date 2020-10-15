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
  parameter bit AsyncOn = 1'b1
) (
  input             clk_i,
  input             rst_ni,
  // native alert from the peripheral
  input             alert_req_i,
  output logic      alert_ack_o,
  // ping input diff pair and ack diff pair
  input alert_rx_t  alert_rx_i,
  // alert output diff pair
  output alert_tx_t alert_tx_o
);


  /////////////////////////////////
  // decode differential signals //
  /////////////////////////////////
  logic ping_sigint, ping_event;

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) i_decode_ping (
    .clk_i,
    .rst_ni,
    .diff_pi  ( alert_rx_i.ping_p     ),
    .diff_ni  ( alert_rx_i.ping_n     ),
    .level_o  (             ),
    .rise_o   (             ),
    .fall_o   (             ),
    .event_o  ( ping_event  ),
    .sigint_o ( ping_sigint )
  );

  logic ack_sigint, ack_level;

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) i_decode_ack (
    .clk_i,
    .rst_ni,
    .diff_pi  ( alert_rx_i.ack_p      ),
    .diff_ni  ( alert_rx_i.ack_n      ),
    .level_o  ( ack_level   ),
    .rise_o   (             ),
    .fall_o   (             ),
    .event_o  (             ),
    .sigint_o ( ack_sigint  )
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
    SigInt,
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
  logic ping_set_d, ping_set_q, ping_clr;

  // if handshake is ongoing, capture additional alert requests
  assign alert_set_d = (alert_clr) ? 1'b0 :  (alert_set_q | alert_req_i);
  assign ping_set_d  = (ping_clr) ? 1'b0 : (ping_set_q | ping_event);

  // alert event acknowledge
  assign alert_ack_o = alert_clr;

  // this FSM performs a full four phase handshake upon a ping or alert trigger.
  // note that the latency of the alert_p/n diff pair is at least one cycle
  // until it enters the receiver FSM. the same holds for the ack_* diff pair
  // input. in case a signal integrity issue is detected, the FSM bails out,
  // sets the alert_p/n diff pair to the same value and toggles it in order to
  // signal that condition over to the receiver.
  always_comb begin : p_fsm
    // default
    state_d = state_q;
    alert_pd   = 1'b0;
    alert_nd   = 1'b1;
    ping_clr   = 1'b0;
    alert_clr  = 1'b0;

    unique case (state_q)
      Idle: begin
        // alert always takes precedence
        if (alert_req_i || alert_set_q || ping_event || ping_set_q) begin
          state_d   = (alert_req_i || alert_set_q) ? AlertHsPhase1 : PingHsPhase1;
          alert_pd  = 1'b1;
          alert_nd  = 1'b0;
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

      // we have a signal integrity issue at one of
      // the incoming diff pairs. this condition is
      // signalled by setting the output diffpair
      // to the same value and continuously toggling
      // them.
      SigInt: begin
        state_d  = Idle;
        if (sigint_detected) begin
          state_d  = SigInt;
          alert_pd = ~alert_pq;
          alert_nd = ~alert_pq;
        end
      end
      // catch parasitic states
      default : state_d = Idle;
    endcase
    // bail out if a signal integrity issue has been detected
    if (sigint_detected && (state_q != SigInt)) begin
      state_d   = SigInt;
      alert_pd  = 1'b0;
      alert_nd  = 1'b0;
      ping_clr  = 1'b0;
      alert_clr = 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
    if (!rst_ni) begin
      state_q     <= Idle;
      alert_pq    <= 1'b0;
      alert_nq    <= 1'b1;
      alert_set_q <= 1'b0;
      ping_set_q  <= 1'b0;
    end else begin
      state_q     <= state_d;
      alert_pq    <= alert_pd;
      alert_nq    <= alert_nd;
      alert_set_q <= alert_set_d;
      ping_set_q  <= ping_set_d;
    end
  end


  ////////////////
  // assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(AlertPKnownO_A, alert_tx_o)

  if (AsyncOn) begin : gen_async_assert
    // check propagation of sigint issues to output within three cycles
    `ASSERT(SigIntPing_A, alert_rx_i.ping_p == alert_rx_i.ping_n [*2] |->
        ##3 alert_tx_o.alert_p == alert_tx_o.alert_n)
    `ASSERT(SigIntAck_A,  alert_rx_i.ack_p == alert_rx_i.ack_n   [*2] |->
        ##3 alert_tx_o.alert_p == alert_tx_o.alert_n)
    // output must be driven diff unless sigint issue detected
    `ASSERT(DiffEncoding_A, (alert_rx_i.ack_p ^ alert_rx_i.ack_n) &&
        (alert_rx_i.ping_p ^ alert_rx_i.ping_n) |->
        ##3 alert_tx_o.alert_p ^ alert_tx_o.alert_n)

    // handshakes can take indefinite time if blocked due to sigint on outgoing
    // lines (which is not visible here). thus, we only check whether the
    // handshake is correctly initiated and defer the full handshake checking to the testbench.
    // TODO: add the staggered cases as well
    `ASSERT(PingHs_A, ##1 $changed(alert_rx_i.ping_p) &&
        (alert_rx_i.ping_p ^ alert_rx_i.ping_n) ##2 state_q == Idle |=>
        $rose(alert_tx_o.alert_p), clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))
  end else begin : gen_sync_assert
    // check propagation of sigint issues to output within one cycle
    `ASSERT(SigIntPing_A, alert_rx_i.ping_p == alert_rx_i.ping_n |=>
        alert_tx_o.alert_p == alert_tx_o.alert_n)
    `ASSERT(SigIntAck_A,  alert_rx_i.ack_p == alert_rx_i.ack_n   |=>
        alert_tx_o.alert_p == alert_tx_o.alert_n)
    // output must be driven diff unless sigint issue detected
    `ASSERT(DiffEncoding_A, (alert_rx_i.ack_p ^ alert_rx_i.ack_n) &&
        (alert_rx_i.ping_p ^ alert_rx_i.ping_n) |=> alert_tx_o.alert_p ^ alert_tx_o.alert_n)
    // handshakes can take indefinite time if blocked due to sigint on outgoing
    // lines (which is not visible here). thus, we only check whether the handshake
    // is correctly initiated and defer the full handshake checking to the testbench.
    `ASSERT(PingHs_A, ##1 $changed(alert_rx_i.ping_p) && state_q == Idle |=>
        $rose(alert_tx_o.alert_p), clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))
  end

  // if alert_req_i is true, handshakes should be continuously repeated
  `ASSERT(AlertHs_A, alert_req_i && state_q == Idle |=> $rose(alert_tx_o.alert_p),
      clk_i, !rst_ni || (alert_tx_o.alert_p == alert_tx_o.alert_n))

endmodule : prim_alert_sender
