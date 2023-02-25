// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for alert_handler_esc_timer.
// Intended to be used with a formal tool.

`include "prim_assert.sv"

module alert_handler_esc_timer_assert_fpv import alert_pkg::*; (
  input  clk_i,
  input  rst_ni,
  input  en_i,
  input  clr_i,
  input  accu_trig_i,
  input  accu_fail_i,
  input  timeout_en_i,
  input [EscCntDw-1:0] timeout_cyc_i,
  input [N_ESC_SEV-1:0] esc_en_i,
  input [N_ESC_SEV-1:0][PHASE_DW-1:0] esc_map_i,
  input [N_PHASES-1:0][EscCntDw-1:0] phase_cyc_i,
  input [PHASE_DW-1:0] crashdump_phase_i,
  input logic latch_crashdump_o,
  input logic esc_trig_o,
  input logic[EscCntDw-1:0] esc_cnt_o,
  input logic[N_ESC_SEV-1:0] esc_sig_req_o,
  input cstate_e esc_state_o
);

  ///////////////////////////////
  // Declarations & Parameters //
  ///////////////////////////////

  // constrain the state-spaces
  localparam int unsigned MAX_TIMEOUT_CYCLES = 10;
  localparam int unsigned MAX_PHASE_CYCLES = 10;

  // symbolic vars for phase map check
  logic [1:0] esc_sel;
  logic [1:0] phase_sel;
  localparam cstate_e Phases [4] = {Phase0, Phase1, Phase2, Phase3};

  // set regs
  logic esc_has_triggered_q;


  /////////////////
  // Assumptions //
  /////////////////

  `ASSUME(TimeoutCycles_M, timeout_cyc_i < MAX_TIMEOUT_CYCLES)
  `ASSUME(TimeoutCyclesConst_M, ##1 $stable(timeout_cyc_i))

  `ASSUME(PhaseCycles_M, phase_cyc_i < MAX_PHASE_CYCLES)
  `ASSUME(PhaseCyclesConst_M, ##1 $stable(phase_cyc_i))

  `ASSUME(CrashdumpPhaseConst_M, ##1 $stable(crashdump_phase_i))

  `ASSUME(EscSelConst_M, ##1 $stable(esc_sel))
  `ASSUME(PhaseSelConst_M, ##1 $stable(phase_sel))

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // if the class is not enabled and we are in IDLE state,
  // neither of the two escalation mechanisms shall fire
  `ASSERT(ClassDisabledNoEscTrig_A, esc_state_o == Idle && !en_i |-> !esc_trig_o)
  `ASSERT(ClassDisabledNoEsc_A, esc_state_o == Idle && !en_i && !alert_handler_esc_timer.fsm_error
          |-> !esc_sig_req_o)
  `ASSERT(EscDisabledNoEsc_A, !esc_en_i[esc_sel] && !alert_handler_esc_timer.fsm_error |->
      !esc_sig_req_o[esc_sel])

  // if timeout counter is enabled due to a pending interrupt, check escalation
  // assume accumulation trigger is not asserted during this sequence
  `ASSERT(TimeoutEscTrig_A, esc_state_o == Idle ##1 en_i && $rose(timeout_en_i) &&
      (timeout_cyc_i > 0) ##1 timeout_en_i [*MAX_TIMEOUT_CYCLES] |=> esc_has_triggered_q,
      clk_i, !rst_ni || accu_trig_i || clr_i || accu_fail_i)

  // check whether an accum trig leads to escalation if enabled
  `ASSERT(AccumEscTrig_A, ##1 en_i && accu_trig_i && esc_state_o inside {Idle, Timeout} |=>
      esc_has_triggered_q, clk_i, !rst_ni || clr_i || accu_fail_i)

  // check escalation cnt and state out
  parameter logic [alert_handler_esc_timer.StateWidth-1:0] StateEncodings [8] = '{
    alert_handler_esc_timer.IdleSt,
    alert_handler_esc_timer.TimeoutSt,
    alert_handler_esc_timer.FsmErrorSt,
    alert_handler_esc_timer.TerminalSt,
    alert_handler_esc_timer.Phase0St,
    alert_handler_esc_timer.Phase1St,
    alert_handler_esc_timer.Phase2St,
    alert_handler_esc_timer.Phase3St
  };
  `ASSERT(EscStateOut_A, alert_handler_esc_timer.state_q == StateEncodings[esc_state_o])
  `ASSERT(EscCntOut_A, alert_handler_esc_timer.u_prim_count.cnt_q[0] == esc_cnt_o)

  // check clr input
  // we cannot use clr to exit from the timeout state
  `ASSERT(ClrCheck_A, clr_i && !(esc_state_o inside {Idle, Timeout, FsmError}) && !accu_fail_i |=>
      esc_state_o == Idle)

  // check escalation map
  `ASSERT(PhaseEscMap_A, esc_state_o == Phases[phase_sel] && esc_map_i[esc_sel] == phase_sel &&
      esc_en_i[esc_sel] |-> esc_sig_req_o[esc_sel])

  // check terminal state is reached eventually if triggered and not cleared
  `ASSERT(TerminalState_A, esc_trig_o |-> strong(##[1:$] esc_state_o == Terminal),
      clk_i, !rst_ni || clr_i || accu_fail_i)

  // check that the crashdump capture trigger is asserted correctly
  `ASSERT(CrashdumpTrigger_A,
      ##1 $changed(esc_state_o) &&
      esc_state_o == cstate_e'(4 + crashdump_phase_i)
      <->
      $past(latch_crashdump_o), esc_state_o == FsmError)

  /////////////////////////
  // Backward Assertions //
  /////////////////////////

  // escalation can only be triggered when in Idle or Timeout state. Trigger mechanisms are either
  // the accumulation trigger or a timeout trigger
  `ASSERT(EscTrigBkwd_A, esc_trig_o |-> esc_state_o inside {Idle, Timeout} && accu_trig_i ||
      esc_state_o == Timeout && esc_cnt_o >= timeout_cyc_i)
  `ASSERT(NoEscTrigBkwd_A, !esc_trig_o |-> !(esc_state_o inside {Idle, Timeout}) ||
      !en_i || !accu_trig_i || !timeout_en_i || clr_i)

  // escalation signals can only be asserted in the escalation phase states, or
  // if we are in the terminal FsmError state
  `ASSERT(EscBkwd_A, esc_sig_req_o[esc_sel] |-> esc_en_i[esc_sel] &&
      esc_has_triggered_q || alert_handler_esc_timer.fsm_error)
  `ASSERT(NoEscBkwd_A, !esc_sig_req_o[esc_sel] |-> !esc_en_i[esc_sel] ||
      esc_state_o != Phases[esc_map_i[esc_sel]] && esc_state_o != FsmError,
      clk_i, !rst_ni || clr_i)

  //////////////////////
  // Helper Processes //
  //////////////////////

  // set registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      esc_has_triggered_q <= 1'b0;
    end else begin
      esc_has_triggered_q <= esc_has_triggered_q & ~clr_i | esc_trig_o;
    end
  end

endmodule : alert_handler_esc_timer_assert_fpv
