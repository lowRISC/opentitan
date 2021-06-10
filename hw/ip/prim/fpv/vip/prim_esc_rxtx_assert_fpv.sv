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
  assign error_present = resp_err_pi ||
                         resp_err_ni ||
                         esc_err_pi  ||
                         esc_err_ni;

  // tracks whether any error has been injected so far
  logic error_d, error_q;
  assign error_d = error_q || error_present;
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_error_reg
    if (!rst_ni) begin
      error_q <= 1'b0;
    end else begin
      error_q <= error_d;
    end
  end

  // tracks whether escalation has been triggered so far
  logic esc_d, esc_q;
  assign esc_d = esc_q || esc_req_i;
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_esc_reg
    if (!rst_ni) begin
      esc_q <= 1'b0;
    end else begin
      esc_q <= esc_d;
    end
  end

  // ping will stay high until ping ok received, then it must be deasserted
  `ASSUME_FPV(PingReqDeassert_M,
      ping_req_i &&
      ping_ok_o
      |=>
      !ping_req_i)
  `ASSUME_FPV(PingReqStaysAsserted0_M,
      ping_req_i &&
      !ping_ok_o
      |=>
      ping_req_i)
  // this timing is guaranteed by the lfsr ping timer.
  `ASSUME_FPV(PingReqStaysLowFor3Cycles_M,
      $fell(ping_req_i)
      |->
      !ping_req_i [*3])


  // assume that escalation enable signal will eventually be deasserted
  // for more than 3 cycles (this assumption is needed such that the FSM liveness
  // assertion below can be proven).
  `ASSUME_FPV(FiniteEsc_M,
      esc_req_i
      |->
      strong(##[1:$] !esc_req_i [*3]))

  // check that ping response time is bounded if no error has occurred so far, and
  // no escalation is being requested.
  `ASSERT(PingRespCheck_A,
      $rose(ping_req_i) &&
      !esc_req_i
      |->
      ##[0:4] ping_ok_o,
      clk_i,
      !rst_ni ||
      error_d ||
      esc_req_i)

  // check escalation response toggles.
  `ASSERT(EscRespCheck_A,
      ##1 esc_req_i
      |->
      ##[0:1] prim_esc_rxtx_fpv.esc_rx_out.resp_p
      ##1 !prim_esc_rxtx_fpv.esc_rx_out.resp_p,
      clk_i,
      !rst_ni ||
      error_present)

  // check correct transmission of escalation within 0-1 cycles
  `ASSERT(EscCheck_A,
      ##1 esc_req_i
      |->
      ##[0:1] esc_en_o,
      clk_i,
      !rst_ni ||
      error_present)

  // check that a single error on the diffpairs is detected
  `ASSERT(SingleSigIntDetected0_A,
      {esc_err_pi, esc_err_ni} == '0 ##1
      $onehot({resp_err_pi, resp_err_ni})
      |->
      integ_fail_o)
  `ASSERT(SingleSigIntDetected1_A,
      $onehot({esc_err_pi, esc_err_ni}) ##1
      {resp_err_pi, resp_err_ni} == '0
      |->
      integ_fail_o)

  // basic liveness of sender FSM
  `ASSERT(FsmLivenessSender_A,
      (prim_esc_rxtx_fpv.u_prim_esc_sender.state_q !=
      prim_esc_rxtx_fpv.u_prim_esc_sender.Idle)
      |->
      strong(##[1:$] (prim_esc_rxtx_fpv.u_prim_esc_sender.state_q
      == prim_esc_rxtx_fpv.u_prim_esc_sender.Idle)))
  // basic liveness of sender FSM (can only be guaranteed if no error is present)
  `ASSERT(FsmLivenessReceiver_A,
      (prim_esc_rxtx_fpv.u_prim_esc_receiver.state_q !=
      prim_esc_rxtx_fpv.u_prim_esc_receiver.Idle)
      |->
      strong(##[1:$] (prim_esc_rxtx_fpv.u_prim_esc_receiver.state_q
      == prim_esc_rxtx_fpv.u_prim_esc_receiver.Idle)),
      clk_i,
      rst_ni ||
      error_present)

  // check that auto escalation timeout does not trigger prematurely.
  // this requires that no errors have been present so far.
  `ASSERT(AutoEscalation0_A,
      ping_req_i &&
      ping_ok_o &&
      !esc_en_o ##1
      !ping_req_i [*0 : 2**prim_esc_rxtx_fpv.u_prim_esc_receiver.TimeoutCntDw - 4]
      |->
      !esc_en_o,
      clk_i,
      !rst_ni ||
      error_d ||
      esc_d)

  // check that auto escalation timeout kicks in if pings are absent for too long.
  // this requires that no errors have been present so far.
  `ASSERT(AutoEscalation1_A,
      ping_req_i &&
      ping_ok_o &&
      !esc_en_o ##1
      !ping_req_i [* 2**prim_esc_rxtx_fpv.u_prim_esc_receiver.TimeoutCntDw - 3 : $]
      |->
      esc_en_o,
      clk_i,
      !rst_ni ||
      error_d ||
      esc_d)


endmodule : prim_esc_rxtx_assert_fpv
