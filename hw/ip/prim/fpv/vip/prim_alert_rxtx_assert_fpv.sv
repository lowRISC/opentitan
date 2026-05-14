// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for alert sender/receiver pair.
//
// This should be bound into a module like prim_alert_rxtx_tb and intended for use with a formal
// tool.

module prim_alert_rxtx_assert_fpv (
  input                        clk_i,
  input                        rst_ni,
  // for sigint error injection only
  input                        ping_err_pi,
  input                        ping_err_ni,
  input                        ack_err_pi,
  input                        ack_err_ni,
  input                        alert_err_pi,
  input                        alert_err_ni,
  // normal I/Os
  input                        alert_test_i,
  input                        alert_req_i,
  input                        alert_ack_o,
  input                        ping_req_i,
  input                        ping_ok_o,
  input                        alert_o
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;

  import prim_mubi_pkg::mubi4_test_true_strict;

  logic error_present;
  assign error_present = ping_err_pi  | ping_err_ni |
                         ack_err_pi   | ack_err_ni  |
                         alert_err_pi | alert_err_ni;

  // The init_trig_i signal being passed to i_prim_alert_receiver (which should cause an
  // initialisation if it is a strict mubi4 true value.
  logic init_trig;
  assign init_trig = prim_mubi_pkg::mubi4_test_true_strict(i_prim_alert_receiver.init_trig_i);

  // True if the environment is asking the receiver to perform initialisation (through the
  // init_trig_i signal) or if the receiver is half-way through such an initialisation.
  logic init_pending;
  assign init_pending = init_trig ||
                        prim_alert_rxtx_tb.i_prim_alert_receiver.state_q inside
                        {
                         prim_alert_rxtx_tb.i_prim_alert_receiver.InitReq,
                         prim_alert_rxtx_tb.i_prim_alert_receiver.InitAckWait
                        };

  logic sender_is_idle, receiver_is_idle, both_idle;
  assign sender_is_idle = prim_alert_rxtx_tb.i_prim_alert_sender.state_q ==
                          prim_alert_rxtx_tb.i_prim_alert_sender.Idle;
  assign receiver_is_idle = prim_alert_rxtx_tb.i_prim_alert_receiver.state_q ==
                            prim_alert_rxtx_tb.i_prim_alert_receiver.Idle;
  assign both_idle = sender_is_idle && receiver_is_idle;
  assign sender_is_pinging = i_prim_alert_sender.state_q inside
                             {i_prim_alert_sender.PingHsPhase1, i_prim_alert_sender.PingHsPhase2};

  // Constrain the environment so that it only injects signal integrity errors by flipping up to one
  // wire (otherwise the module has no way to detect them).
  PingErrorsAreOH_M:  assume property ($onehot0({ping_err_pi, ping_err_ni}));
  AckErrorsAreOH_M:   assume property ($onehot0({ack_err_pi, ack_err_ni}));
  AlertErrorsAreOH_M: assume property ($onehot0({alert_err_pi, alert_err_ni}));

  // Another constraint on the environment is that it will hold a ping request high until a ping ok
  // is received, at which point it is deasserted.
  //
  // The PingEn_M assumption asks that if ping_req_i rises then it will stay high until the cycle
  // after ping_ok_o or error_present is true, at which point it will drop.
  //
  //   TODO: This excludes the case where no ping ok will be returned due to an error
  //
  // The PingDeassert_M asks that ping_req_i will always drop on the cycle after ping_ok_o is true.
  PingEn_M: assume property ($rose(ping_req_i) |->
                             ping_req_i throughout (ping_ok_o || error_present)[->1] ##1
                             $fell(ping_req_i));

  PingDeassert_M: assume property (ping_req_i && ping_ok_o |=> !ping_req_i);

  // The alert signal being sent from the alert sender
  logic sender_alert_level;
  assign sender_alert_level = i_prim_alert_sender.alert_tx_o.alert_p &
                              ~i_prim_alert_sender.alert_tx_o.alert_n;

  // The alert sender's view of the ack signal that was sent from the alert receiver.
  logic sender_ack_level;
  assign sender_ack_level = i_prim_alert_sender.alert_rx_i.ack_p &
                            ~i_prim_alert_sender.alert_rx_i.ack_n;

  // The ping signal being sent from the alert receiver
  logic receiver_ping_level;
  assign receiver_ping_level = i_prim_alert_receiver.alert_rx_o.ping_p &
                               ~i_prim_alert_receiver.alert_rx_o.ping_n;

  // Handshake assertions
  //
  // These assertions track "handshakes". Normally this has the sender signalling something and the
  // receiver responding, but the ping handshake goes the other way around. To avoid situations
  // where the blocks are starting in the wrong state, the precondition for the assertions requires
  // both sender and receiver to be in the idle state.
  //
  // The "if (1)" part is to provide a block that can hold the "default disable iff" setting.
  if (1) begin : gen_handshakes
    // Assertions about handshakes should be disabled if any error has been injected into the
    // signals. Injecting errors onto the bus can stop the handshake working, but that isn't the
    // behaviour we're trying to reason about.
    default disable iff !rst_ni || error_present || init_pending;

    // This is the alert handshake. Because this is in a synchronous context, the timing of the
    // sequence is simple.
    sequence FullHandshake_S;
      $rose(sender_alert_level)                                ##1
      $stable(sender_alert_level) && $rose(sender_ack_level)   ##1
      $fell(sender_alert_level)   && $stable(sender_ack_level) ##1
      $stable(sender_alert_level) && $fell(sender_ack_level);
    endsequence

    PingHs_A: assert property (##1 $changed(receiver_ping_level) && both_idle |=> FullHandshake_S);

    AlertHs_A: assert property (alert_req_i && both_idle |=> (FullHandshake_S ##0 alert_ack_o));

    AlertTestHs_A: assert property (alert_test_i && both_idle |=> FullHandshake_S);

    AlertReqAck_A: assert property (alert_req_i && both_idle |=> s_eventually alert_ack_o);

    // If the alert receiver is asked to ping the alert sender when that block isn't already
    // responding to a ping, the ping transaction will go through and the receiver will respond with
    // ping_ok_o in at most 10 cycles.
    AlertPingOk_A: assert property (!sender_is_pinging && $rose(ping_req_i) |-> ##[1:9] ping_ok_o);

    // If there is an alert request (a genuine alert or a test) sent to the alert sender, we
    // normally expect the alert receiver to report it through alert_o on the next cycle.
    //
    // This is intended to describe the "good case", where there isn't any recent or overlapping
    // ping request.
    AlertCheck0_A: assert property (!ping_req_i [*3] ##0
                                    sender_is_idle && $rose(alert_req_i | alert_test_i) |=>
                                    alert_o);

    // A liveness assertion for the FSM in the alert sender and receiver, saying that they always
    // get back to the idle state eventually (assuming there hasn't been an injected error).
    FsmLivenessSender_A: assert property (s_eventually (sender_is_idle));
    FsmLivenessReceiver_A: assert property (s_eventually (receiver_is_idle));
  end

  // The full version of the alert check allows ping collisions, unlike AlertCheck0_A. This says
  // that if an alert has been requested then the receiver's alert_o output will go high as soon as
  // there is a cycle with the sender idle and no ping request.
  AlertCheck1_A: assert property (disable iff (!rst_ni || error_present || init_trig ||
                                               i_prim_alert_sender.alert_clr)
                                  alert_req_i | alert_test_i |=>
                                  ##[1:$] (sender_is_idle && !ping_req_i) ##1 alert_o);

  // The in-band reset signalled through the receiver's init_trig_i port is guaranteed to move the
  // alert sender FSM to the idle state in bounded time (20 cycles), so long as no error has been
  // injected.
  InBandInit_A: assert property (disable iff (!rst_ni || error_present)
                                 init_trig |-> ##[1:20] sender_is_idle);
endmodule
