// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for alert sender/receiver pair. Intended to use with
// a formal tool.

`include "prim_assert.sv"

module prim_alert_rxtx_assert_fpv (
  input        clk_i,
  input        rst_ni,
  // for sigint error injection only
  input        ping_err_pi,
  input        ping_err_ni,
  input        ack_err_pi,
  input        ack_err_ni,
  input        alert_err_pi,
  input        alert_err_ni,
  // normal I/Os
  input        alert_req_i,
  input        alert_ack_o,
  input        ping_req_i,
  input        ping_ok_o,
  input        integ_fail_o,
  input        alert_o
);

  logic error_present;
  assign error_present = ping_err_pi  | ping_err_ni |
                         ack_err_pi   | ack_err_ni  |
                         alert_err_pi | alert_err_ni;

  // note: we can only detect sigint errors where one wire is flipped.
  `ASSUME_FPV(PingErrorsAreOH_M,  $onehot0({ping_err_pi, ping_err_ni}),   clk_i, !rst_ni)
  `ASSUME_FPV(AckErrorsAreOH_M,   $onehot0({ack_err_pi, ack_err_ni}),     clk_i, !rst_ni)
  `ASSUME_FPV(AlertErrorsAreOH_M, $onehot0({alert_err_pi, alert_err_ni}), clk_i, !rst_ni)

  // ping will stay high until ping ok received, then it must be deasserted
  // TODO: this excludes the case where no ping ok will be returned due to an error
  `ASSUME_FPV(PingDeassert_M, ping_req_i && ping_ok_o |=> !ping_req_i, clk_i, !rst_ni)
  `ASSUME_FPV(PingEn_M, $rose(ping_req_i) |-> ping_req_i throughout
      (ping_ok_o || error_present)[->1] ##1 $fell(ping_req_i),
      clk_i, !rst_ni)
  sequence FullHandshake_S;
    $rose(prim_alert_rxtx_fpv.alert_tx_out.alert_p)   ##1
    $rose(prim_alert_rxtx_fpv.alert_rx_out.ack_p)     &&
    $stable(prim_alert_rxtx_fpv.alert_tx_out.alert_p) ##1
    $fell(prim_alert_rxtx_fpv.alert_tx_out.alert_p)   &&
    $stable(prim_alert_rxtx_fpv.alert_rx_out.ack_p)   ##1
    $fell(prim_alert_rxtx_fpv.alert_rx_out.ack_p)     &&
    $stable(prim_alert_rxtx_fpv.alert_tx_out.alert_p) ;
  endsequence

  // note: injected errors may lockup the FSMs, and hence the full HS can
  // only take place if both FSMs are in a sane state
  `ASSERT(PingHs_A, ##1 $changed(prim_alert_rxtx_fpv.alert_rx_out.ping_p) &&
      (prim_alert_rxtx_fpv.i_prim_alert_sender.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_sender.Idle) &&
      (prim_alert_rxtx_fpv.i_prim_alert_receiver.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_receiver.Idle)|=> FullHandshake_S,
      clk_i, !rst_ni || error_present)
  `ASSERT(AlertHs_A, alert_req_i &&
      (prim_alert_rxtx_fpv.i_prim_alert_sender.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_sender.Idle) &&
      (prim_alert_rxtx_fpv.i_prim_alert_receiver.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_receiver.Idle) |=>
      FullHandshake_S |-> alert_ack_o, clk_i, !rst_ni || error_present)

  // transmission of pings
  // note: the complete transmission of pings only happen when no ping handshake is in progress
  `ASSERT(AlertPingOk_A, !(prim_alert_rxtx_fpv.i_prim_alert_sender.state_q inside {
      prim_alert_rxtx_fpv.i_prim_alert_sender.PingHsPhase1,
      prim_alert_rxtx_fpv.i_prim_alert_sender.PingHsPhase2}) && $rose(ping_req_i) |->
      ##[1:9] ping_ok_o, clk_i, !rst_ni || error_present)
  `ASSERT(AlertPingIgnored_A, (prim_alert_rxtx_fpv.i_prim_alert_sender.state_q inside {
      prim_alert_rxtx_fpv.i_prim_alert_sender.PingHsPhase1,
      prim_alert_rxtx_fpv.i_prim_alert_sender.PingHsPhase2}) && $rose(ping_req_i) |->
      ping_ok_o == 0 throughout ping_req_i [->1], clk_i, !rst_ni || error_present)
  // transmission of alerts in case of no collision with ping enable
  `ASSERT(AlertCheck0_A, !ping_req_i [*3] ##0 $rose(alert_req_i) &&
      (prim_alert_rxtx_fpv.i_prim_alert_sender.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_sender.Idle) |=>
      alert_o, clk_i, !rst_ni || error_present || ping_req_i)
  // transmission of alerts in the general case which can include continous ping collisions
  `ASSERT(AlertCheck1_A, alert_req_i |=>
      strong(##[1:$] ((prim_alert_rxtx_fpv.i_prim_alert_sender.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_sender.Idle) && !ping_req_i) ##1 alert_o),
      clk_i, !rst_ni || error_present || alert_ack_o)

  // basic liveness of FSMs in case no errors are present
  `ASSERT(FsmLivenessSender_A,
      (prim_alert_rxtx_fpv.i_prim_alert_sender.state_q !=
      prim_alert_rxtx_fpv.i_prim_alert_sender.Idle) |->
      strong(##[1:$] (prim_alert_rxtx_fpv.i_prim_alert_sender.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_sender.Idle)), clk_i, !rst_ni || error_present)
  `ASSERT(FsmLivenessReceiver_A,
      (prim_alert_rxtx_fpv.i_prim_alert_receiver.state_q !=
      prim_alert_rxtx_fpv.i_prim_alert_receiver.Idle) |->
      strong(##[1:$] (prim_alert_rxtx_fpv.i_prim_alert_receiver.state_q ==
      prim_alert_rxtx_fpv.i_prim_alert_receiver.Idle)),clk_i, !rst_ni || error_present)

endmodule : prim_alert_rxtx_assert_fpv
