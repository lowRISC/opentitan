// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for escalation sender/receiver pair. Intended to use with
// a formal tool.

`include "prim_assert.sv"

module prim_esc_rxtx_assert_fpv (
  input        clk_i,
  input        rst_ni,
  // for sigint error injection only
  input        resp_err_pi,
  input        resp_err_ni,
  input        esc_err_pi,
  input        esc_err_ni,
  // normal I/Os
  input        esc_req_i,
  input        ping_req_i,
  input        ping_ok_o,
  input        integ_fail_o,
  input        esc_en_o
);

  logic error_present;
  assign error_present = resp_err_pi | resp_err_ni |
                         esc_err_pi  | esc_err_ni;

  // ping will stay high until ping ok received, then it must be deasserted
  // TODO: this escludes the case where no ping ok will be returned due to an error
  `ASSUME_FPV(PingDeassert_M, ping_req_i && ping_ok_o |=> ping_req_i, clk_i, !rst_ni)
  `ASSUME_FPV(PingEnStaysAsserted0_M, ping_req_i |=>
      (ping_req_i && !ping_ok_o) or (ping_req_i && ping_ok_o ##1 $fell(ping_req_i)),
      clk_i, !rst_ni || error_present)

  // assume that the ping enable and escalation enable signals will eventually be deasserted (and
  // esc will stay low for more than 2 cycles)
  `ASSUME_FPV(FiniteEsc_M, esc_req_i |-> strong(##[1:$] !esc_req_i [*2]))
  `ASSUME_FPV(FinitePing_M, ping_req_i |-> strong(##[1:$] !ping_req_i))

  // ping response mus occur within 4 cycles (given that no
  // error occured within the previous cycles)
  `ASSERT(PingRespCheck_A, !error_present [*4] ##1 $rose(ping_req_i) |->
      ##[0:4] ping_ok_o, clk_i, !rst_ni || error_present)

  // be more specific (i.e. use throughout)
  `ASSERT(EscRespCheck_A, ##1 esc_req_i |-> ##[0:1] prim_esc_rxtx_fpv.esc_rx_out.resp_p ##1
      !prim_esc_rxtx_fpv.esc_rx_out.resp_p, clk_i, !rst_ni || error_present)

  // check correct transmission of escalation within 0-1 cycles
  `ASSERT(EscCheck_A, ##1 esc_req_i |-> ##[0:1] esc_en_o, clk_i, !rst_ni || error_present)

  // check that a single error on the diffpairs is detected
  `ASSERT(SingleSigIntDetected0_A, {esc_err_pi, esc_err_ni} == '0 ##1
      $onehot({resp_err_pi, resp_err_ni}) |-> integ_fail_o)
  `ASSERT(SingleSigIntDetected1_A, $onehot({esc_err_pi, esc_err_ni}) ##1
      {resp_err_pi, resp_err_ni} == '0 |-> integ_fail_o)

  // basic liveness of FSMs in case no errors are present
  `ASSERT(FsmLivenessSender_A, (prim_esc_rxtx_fpv.i_prim_esc_sender.state_q !=
      prim_esc_rxtx_fpv.i_prim_esc_sender.Idle) |->
      strong(##[1:$] (prim_esc_rxtx_fpv.i_prim_esc_sender.state_q
      == prim_esc_rxtx_fpv.i_prim_esc_sender.Idle)), clk_i, !rst_ni || error_present)
  `ASSERT(FsmLivenessReceiver_A, (prim_esc_rxtx_fpv.i_prim_esc_receiver.state_q !=
      prim_esc_rxtx_fpv.i_prim_esc_receiver.Idle) |->
      strong(##[1:$] (prim_esc_rxtx_fpv.i_prim_esc_receiver.state_q
      == prim_esc_rxtx_fpv.i_prim_esc_receiver.Idle)), clk_i, !rst_ni || error_present)

endmodule : prim_esc_rxtx_assert_fpv
