// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements the escalation timer, which times the four escalation
// phases. There are two mechanisms that can trigger the escalation protocol:
//
// 1) via accum_trigger_i, which will be asserted once the accumulator value
//    exceeds a programmable amount of alert occurences.
//
// 2) via an interrupt timeout, if this is enabled. If this functionality is
//    enabled, the internal escalation counter is reused to check whether the
//    interrupt times out. If it does time out, the outcome is the same as if
//    accum_trigger_i where asserted.
//
// Note that escalation always takes precedence over the interrupt timeout.
//

`include "prim_assert.sv"

module alert_handler_esc_timer import alert_pkg::*; (
  input                        clk_i,
  input                        rst_ni,
  input                        en_i,           // enables timeout/escalation
  input                        clr_i,          // aborts escalation
  input                        accum_trig_i,   // this will trigger escalation
  input                        timeout_en_i,   // enables timeout
  input        [EscCntDw-1:0]  timeout_cyc_i,  // interrupt timeout. 0 = disabled
  input        [N_ESC_SEV-1:0] esc_en_i,       // escalation signal enables
  input        [N_ESC_SEV-1:0]
               [PHASE_DW-1:0]  esc_map_i,      // escalation signal / phase map
  input        [N_PHASES-1:0]
               [EscCntDw-1:0]  phase_cyc_i,    // cycle counts of individual phases
  output logic                 esc_trig_o,     // asserted if escalation triggers
  output logic [EscCntDw-1:0]  esc_cnt_o,      // current timeout / escalation count
  output logic [N_ESC_SEV-1:0] esc_sig_req_o,  // escalation signal outputs
  // current state output
  // 000: idle, 001: irq timeout counting 100: phase0, 101: phase1, 110: phase2, 111: phase3
  output cstate_e              esc_state_o
);

  /////////////
  // Counter //
  /////////////

  cstate_e state_d, state_q;

  logic cnt_en, cnt_clr, cnt_ge;
  logic [EscCntDw-1:0] cnt_d, cnt_q;

  // escalation counter, used for all phases and the timeout
  assign cnt_d = cnt_q + 1'b1;

  // current state output
  assign esc_state_o = state_q;
  assign esc_cnt_o   = cnt_q;

  // threshold test, the thresholds are muxed further below
  // depending on the current state
  logic [EscCntDw-1:0] thresh;
  assign cnt_ge    = (cnt_q >= thresh);

  //////////////
  // Main FSM //
  //////////////

  logic [N_PHASES-1:0] phase_oh;

  always_comb begin : p_fsm
    // default
    state_d    = state_q;
    cnt_en     = 1'b0;
    cnt_clr    = 1'b0;
    esc_trig_o = 1'b0;
    phase_oh   = '0;
    thresh     = timeout_cyc_i;

    unique case (state_q)
      // wait for an escalation trigger or an alert trigger
      // the latter will trigger an interrupt timeout
      Idle: begin
        cnt_clr = 1'b1;

        if (accum_trig_i && en_i && !clr_i) begin
          state_d    = Phase0;
          cnt_en     = 1'b1;
          esc_trig_o = 1'b1;
        // the counter is zero in this state. so if the
        // timeout count is zero (==disabled), cnt_ge will be true.
        end else if (timeout_en_i && !cnt_ge && en_i) begin
          cnt_en  = 1'b1;
          state_d = Timeout;
        end
      end
      // we are in interrupt timeout state
      // in case an escalation comes in, we immediately have to
      // switch over to the first escalation phase.
      // in case the interrupt timeout hits it's cycle count, we
      // also enter escalation phase0.
      // ongoing timeouts can always be cleared.
      Timeout: begin
        if ((accum_trig_i && en_i && !clr_i) || (cnt_ge && timeout_en_i)) begin
          state_d    = Phase0;
          cnt_en     = 1'b1;
          cnt_clr    = 1'b1;
          esc_trig_o = 1'b1;
        // the timeout enable is connected to the irq state
        // if that is cleared, stop the timeout counter
        end else if (timeout_en_i) begin
          cnt_en  = 1'b1;
        end else begin
          state_d = Idle;
          cnt_clr = 1'b1;
        end
      end
      // note: autolocking the clear signal is done in the regfile
      Phase0: begin
        cnt_en      = 1'b1;
        phase_oh[0] = 1'b1;
        thresh      = phase_cyc_i[0];

        if (clr_i) begin
          state_d = Idle;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Phase1;
          cnt_clr = 1'b1;
          cnt_en  = 1'b1;
        end
      end
      Phase1: begin
        cnt_en      = 1'b1;
        phase_oh[1] = 1'b1;
        thresh      = phase_cyc_i[1];

        if (clr_i) begin
          state_d = Idle;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Phase2;
          cnt_clr = 1'b1;
          cnt_en  = 1'b1;
        end
      end
      Phase2: begin
        cnt_en      = 1'b1;
        phase_oh[2] = 1'b1;
        thresh      = phase_cyc_i[2];

        if (clr_i) begin
          state_d = Idle;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Phase3;
          cnt_clr = 1'b1;
        end
      end
      Phase3: begin
        cnt_en      = 1'b1;
        phase_oh[3] = 1'b1;
        thresh      = phase_cyc_i[3];

        if (clr_i) begin
          state_d = Idle;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Terminal;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end
      end
      // final, terminal state after escalation.
      // if clr is locked down, only a system reset
      // will get us out of this state
      Terminal: begin
        cnt_clr = 1'b1;
        if (clr_i) begin
          state_d = Idle;
        end
      end
      default: state_d = Idle;
    endcase
  end

  logic [N_ESC_SEV-1:0][N_PHASES-1:0] esc_map_oh;
  for (genvar k = 0; k < N_ESC_SEV; k++) begin : gen_phase_map
    // generate configuration mask for escalation enable signals
    assign esc_map_oh[k] = N_ESC_SEV'(esc_en_i[k]) << esc_map_i[k];
    // mask reduce current phase state vector
    assign esc_sig_req_o[k] = |(esc_map_oh[k] & phase_oh);
  end

  ///////////////
  // Registers //
  ///////////////

  // switch interrupt / escalation mode
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= Idle;
      cnt_q   <= '0;
    end else begin
      state_q <= state_d;

      // escalation counter
      if (cnt_en && cnt_clr) begin
        cnt_q <= EscCntDw'(1'b1);
      end else if (cnt_clr) begin
        cnt_q <= '0;
      end else if (cnt_en) begin
        cnt_q <= cnt_d;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // a clear should always bring us back to idle
  `ASSERT(CheckClr, clr_i && !(state_q inside {Idle, Timeout}) |=>
      state_q == Idle)
  // if currently in idle and not enabled, must remain here
  `ASSERT(CheckEn,  state_q == Idle && !en_i |=>
      state_q == Idle)
  // Check if accumulation trigger correctly captured
  `ASSERT(CheckAccumTrig0,  accum_trig_i && state_q == Idle && en_i && !clr_i |=>
      state_q == Phase0)
  `ASSERT(CheckAccumTrig1,  accum_trig_i && state_q == Timeout && en_i && !clr_i |=>
      state_q == Phase0)
  // Check if timeout correctly captured
  `ASSERT(CheckTimeout0, state_q == Idle && timeout_en_i && en_i && timeout_cyc_i != 0 &&
      !accum_trig_i |=> state_q == Timeout)
  `ASSERT(CheckTimeout1, state_q == Timeout && timeout_en_i && cnt_q < timeout_cyc_i &&
      !accum_trig_i |=> state_q == Timeout)
  `ASSERT(CheckTimeout2, state_q == Timeout && !timeout_en_i && !accum_trig_i |=>
      state_q == Idle)
  // Check if timeout correctly triggers escalation
  `ASSERT(CheckTimeoutTrig, state_q == Timeout && timeout_en_i &&
      cnt_q == timeout_cyc_i |=> state_q == Phase0)
  // Check whether escalation phases are correctly switched
  `ASSERT(CheckPhase0, state_q == Phase0 && !clr_i && cnt_q >= phase_cyc_i[0] |=>
      state_q == Phase1)
  `ASSERT(CheckPhase1, state_q == Phase1 && !clr_i && cnt_q >= phase_cyc_i[1] |=>
      state_q == Phase2)
  `ASSERT(CheckPhase2, state_q == Phase2 && !clr_i && cnt_q >= phase_cyc_i[2] |=>
      state_q == Phase3)
  `ASSERT(CheckPhase3, state_q == Phase3 && !clr_i && cnt_q >= phase_cyc_i[3] |=>
      state_q == Terminal)

endmodule : alert_handler_esc_timer
