// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The alert sender primitive module differentially encodes and transmits an
// alert signal to the prim_alert_receiver module. An alert will be signalled
// by a full handshake on alert_po/no and ack_pi/ni. The alert_i signal may
// be continuously asserted, in which case the alert signalling handshake
// will be repeatedly initiated.
//
// Further, this module supports in-band ping testing, which means that a level
// change on the ping_pi/ni diff pair will result in a full-handshake response
// on alert_po/no and ack_pi/ni.
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

module prim_alert_sender #(
  // enables additional synchronization logic
  parameter bit AsyncOn = 1'b1
) (
  input        clk_i,
  input        rst_ni,
  // native alert from the peripheral
  input        alert_i,
  // ping input diff pair
  input        ping_pi,
  input        ping_ni,
  // alert input diff pair
  input        ack_pi,
  input        ack_ni,
  // alert output diff pair
  output logic alert_po,
  output logic alert_no
);

  //////////////////////////////////////////////////////
  // decode differential signals
  //////////////////////////////////////////////////////
  logic ping_sigint, ping_event;

  prim_diff_decode #(
    .AsyncOn(AsyncOn)
  ) i_decode_ping (
    .clk_i,
    .rst_ni,
    .diff_pi  ( ping_pi     ),
    .diff_ni  ( ping_ni     ),
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
    .diff_pi  ( ack_pi      ),
    .diff_ni  ( ack_ni      ),
    .level_o  ( ack_level   ),
    .rise_o   (             ),
    .fall_o   (             ),
    .event_o  (             ),
    .sigint_o ( ack_sigint  )
  );

  //////////////////////////////////////////////////////
  // main protocol FSM that drives the diff output
  //////////////////////////////////////////////////////
  typedef enum logic [2:0] {Idle, HsPhase1, HsPhase2, SigInt, Pause0, Pause1} state_e;
  state_e state_d, state_q;
  logic alert_pq, alert_nq, alert_pd, alert_nd;
  logic sigint_detected;

  assign sigint_detected = ack_sigint | ping_sigint;

  // diff pair output
  assign alert_po = alert_pq;
  assign alert_no = alert_nq;

  // alert and ping set regs
  logic alert_set_d, alert_set_q, alert_clr;
  logic ping_set_d, ping_set_q, ping_clr;
  assign alert_set_d = (alert_clr) ? 1'b0 :  (alert_set_q | alert_i);
  assign ping_set_d  = (ping_clr) ? 1'b0 : (ping_set_q | ping_event);

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
        if (alert_i || alert_set_q || ping_event || ping_set_q) begin
          state_d   = HsPhase1;
          alert_pd  = 1'b1;
          alert_nd  = 1'b0;
          if (ping_event || ping_set_q) begin
            ping_clr  = 1'b1;
          end else begin
            alert_clr = 1'b1;
          end
        end
      end
      // waiting for ack from receiver
      HsPhase1: begin
        if (ack_level) begin
          state_d  = HsPhase2;
        end else begin
          alert_pd = 1'b1;
          alert_nd = 1'b0;
        end
      end
      // wait for deassertion of ack
      HsPhase2: begin
        if (!ack_level) begin
          state_d = Pause0;
        end
      end
      // pause cycles between back-to-back handshakes
      Pause0: state_d = Pause1;
      Pause1: state_d = Idle;
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

  //////////////////////////////////////////////////////
  // assertions
  //////////////////////////////////////////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(AlertPKnownO_A, alert_po, clk_i, !rst_ni)
  `ASSERT_KNOWN(AlertNKnownO_A, alert_no, clk_i, !rst_ni)

  if (AsyncOn) begin : gen_async_assert
    // check propagation of sigint issues to output within three cycles
    `ASSERT(SigIntPing_A, ping_pi == ping_ni [*2] |-> ##3 alert_po == alert_no, clk_i, !rst_ni)
    `ASSERT(SigIntAck_A,  ack_pi == ack_ni   [*2] |-> ##3 alert_po == alert_no, clk_i, !rst_ni)
    // output must be driven diff unless sigint issue detected
    `ASSERT(DiffEncoding_A, (ack_pi ^ ack_ni) && (ping_pi ^ ping_ni) |->
        ##3 alert_po ^ alert_no, clk_i, !rst_ni)

    // handshakes can take indefinite time if blocked due to sigint on outgoing
    // lines (which is not visible here). thus, we only check whether the handshake is correctly initiated
    // and defer the full handshake checking to the testbench.
    // TODO: add the staggered cases as well
    `ASSERT(PingHs_A, ##1 $changed(ping_pi) && (ping_pi ^ ping_ni) ##2 state_q == Idle |=>
        $rose(alert_po), clk_i, !rst_ni || (alert_po == alert_no))
  end else begin : gen_sync_assert
    // check propagation of sigint issues to output within one cycle
    `ASSERT(SigIntPing_A, ping_pi == ping_ni |=> alert_po == alert_no, clk_i, !rst_ni)
    `ASSERT(SigIntAck_A,  ack_pi == ack_ni   |=> alert_po == alert_no, clk_i, !rst_ni)
    // output must be driven diff unless sigint issue detected
    `ASSERT(DiffEncoding_A, (ack_pi ^ ack_ni) && (ping_pi ^ ping_ni) |=> alert_po ^ alert_no,
        clk_i, !rst_ni)
    // handshakes can take indefinite time if blocked due to sigint on outgoing
    // lines (which is not visible here). thus, we only check whether the handshake is correctly initiated
    // and defer the full handshake checking to the testbench.
    `ASSERT(PingHs_A, ##1 $changed(ping_pi) && state_q == Idle |=> $rose(alert_po),
        clk_i, !rst_ni || (alert_po == alert_no))
  end

  // if alert_i is true, handshakes should be continuously repeated
  `ASSERT(AlertHs_A, alert_i && state_q == Idle |=> $rose(alert_po),
      clk_i, !rst_ni || (alert_po == alert_no))

endmodule : prim_alert_sender
