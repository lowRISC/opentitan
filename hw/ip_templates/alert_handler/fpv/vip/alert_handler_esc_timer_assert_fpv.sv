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
  input  accum_trig_i,
  input  timeout_en_i,
  input [EscCntDw-1:0] timeout_cyc_i,
  input [N_ESC_SEV-1:0] esc_en_i,
  input [N_ESC_SEV-1:0][PHASE_DW-1:0] esc_map_i,
  input [N_PHASES-1:0][EscCntDw-1:0] phase_cyc_i,
  input logic esc_trig_o,
  input logic[EscCntDw-1:0] esc_cnt_o,
  input logic[N_ESC_SEV-1:0] esc_sig_en_o,
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
  localparam cstate_e phases [4] = {Phase0, Phase1, Phase2, Phase3};

  // set regs
  logic esc_has_triggered_q;


  /////////////////
  // Assumptions //
  /////////////////

  `ASSUME(TimeoutCycles_M, timeout_cyc_i < MAX_TIMEOUT_CYCLES)
  `ASSUME(TimeoutCyclesConst_M, ##1 $stable(timeout_cyc_i))

  `ASSUME(PhaseCycles_M, phase_cyc_i < MAX_PHASE_CYCLES)
  `ASSUME(PhaseCyclesConst_M, ##1 $stable(phase_cyc_i))

  `ASSUME(EscSelConst_M, ##1 $stable(esc_sel))
  `ASSUME(PhaseSelConst_M, ##1 $stable(phase_sel))

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // if the class is not enabled and we are in IDLE state,
  // neither of the two escalation mechanisms shall fire
  `ASSERT(ClassDisabledNoEscTrig_A, esc_state_o == Idle && !en_i |-> !esc_trig_o)
  `ASSERT(ClassDisabledNoEsc_A, esc_state_o == Idle && !en_i |-> !esc_sig_en_o)
  `ASSERT(EscDisabledNoEsc_A, !esc_en_i[esc_sel] |-> !esc_sig_en_o[esc_sel])

  // if timeout counter is enabled due to a pending interrupt, check escalation
  // assume accumulation trigger is not asserted during this sequence
  `ASSERT(TimeoutEscTrig_A, ##1 en_i && $rose(timeout_en_i) && (timeout_cyc_i > 0) ##1
      timeout_en_i [*MAX_TIMEOUT_CYCLES] |=> esc_has_triggered_q,
      clk_i, !rst_ni || accum_trig_i || clr_i)

  // check whether an accum trig leads to escalation if enabled
  `ASSERT(AccumEscTrig_A, ##1 en_i && accum_trig_i && esc_state_o inside {Idle, Timeout} |=>
      esc_has_triggered_q)

  // check escalation cnt and state out
  `ASSERT(EscStateOut_A, alert_handler_esc_timer.state_q == esc_state_o)
  `ASSERT(EscCntOut_A, alert_handler_esc_timer.cnt_q == esc_cnt_o)

  // check clr input
  // we cannot use clr to exit from the timeout state
  `ASSERT(ClrCheck_A, clr_i && !(esc_state_o inside {Idle, Timeout}) |=>
      esc_state_o == Idle)

  // check escalation map
  `ASSERT(PhaseEscMap_A, esc_state_o == phases[phase_sel] && esc_map_i[esc_sel] == phase_sel &&
      esc_en_i[esc_sel] |-> esc_sig_en_o[esc_sel])

  // check terminal state is reached eventually if triggered and not cleared
  `ASSERT(TerminalState_A, esc_trig_o |-> strong(##[1:$] esc_state_o == Terminal),
      clk_i, !rst_ni || clr_i)

  /////////////////////////
  // Backward Assertions //
  /////////////////////////

  // escalation can only be triggered when in Idle or Timeout state. Trigger mechanisms are either
  // the accumulation trigger or a timeout trigger
  `ASSERT(EscTrigBkwd_A, esc_trig_o |-> esc_state_o inside {Idle, Timeout} && accum_trig_i ||
      esc_state_o  == Timeout && esc_cnt_o >= timeout_cyc_i)
  `ASSERT(NoEscTrigBkwd_A, !esc_trig_o |-> !(esc_state_o inside {Idle, Timeout}) ||
      (!en_i || !accum_trig_i || !timeout_en_i))

  // escalation signals can only be asserted in the escalation phase states
  `ASSERT(EscBkwd_A, esc_sig_en_o[esc_sel] |-> esc_en_i[esc_sel] &&
      esc_has_triggered_q)
  `ASSERT(NoEscBkwd_A, !esc_sig_en_o[esc_sel] |-> !esc_en_i[esc_sel] ||
      esc_state_o != phases[esc_map_i[esc_sel]], clk_i, !rst_ni || clr_i)

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
