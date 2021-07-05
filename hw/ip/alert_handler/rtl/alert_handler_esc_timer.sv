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
  input                        accu_trig_i,    // this will trigger escalation
  input                        accu_fail_i,    // this will move the FSM into a terminal error state
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

  ////////////////////
  // Tandem Counter //
  ////////////////////

  logic cnt_en, cnt_clr, cnt_ge;
  logic [1:0][EscCntDw-1:0] cnt_q;

  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // the FSM below is moved into a terminal error state and escalation actions
  // are permanently asserted.
  for (genvar k = 0; k < 2; k++) begin : gen_double_cnt

    logic cnt_en_buf, cnt_clr_buf;

    // These size_only buffers are instantiated in order to prevent
    // optimization / merging of the two counters.
    prim_buf u_prim_buf_clr (
      .in_i(cnt_clr),
      .out_o(cnt_clr_buf)
    );

    prim_buf u_prim_buf_en (
      .in_i(cnt_en),
      .out_o(cnt_en_buf)
    );

    // escalation counter, used for all phases and the timeout
    logic [EscCntDw-1:0] cnt_d;
    assign cnt_d = (cnt_clr_buf && cnt_en_buf) ? EscCntDw'(1'b1) :
                   (cnt_clr_buf)               ? '0              :
                   (cnt_en_buf)                ? cnt_q[k] + 1'b1 : cnt_q[k];

    prim_flop #(
      .Width(EscCntDw)
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i(cnt_d),
      .q_o(cnt_q[k])
    );
  end

  // threshold test, the thresholds are muxed further below
  // depending on the current state
  logic [EscCntDw-1:0] thresh;
  assign cnt_ge    = (cnt_q[0] >= thresh);

  // current counter output
  assign esc_cnt_o   = cnt_q[0];

  // consistency check
  logic cnt_check_fail;
  assign cnt_check_fail = cnt_q[0] != cnt_q[1];

  //////////////
  // Main FSM //
  //////////////

  logic [N_PHASES-1:0] phase_oh;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 8 -n 10 \
  //      -s 784905746 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (42.86%)
  //  6: |||||||||||||||||||| (42.86%)
  //  7: |||||| (14.29%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    IdleSt     = 10'b1101000111,
    TimeoutSt  = 10'b0010011110,
    Phase0St   = 10'b1111011001,
    Phase1St   = 10'b0001110100,
    Phase2St   = 10'b1110110010,
    Phase3St   = 10'b0010000001,
    TerminalSt = 10'b0101101010,
    FsmErrorSt = 10'b1000101101
  } state_e;

  logic fsm_error;
  state_e state_d, state_q;

  always_comb begin : p_fsm
    // default
    state_d     = state_q;
    esc_state_o = Idle;
    cnt_en      = 1'b0;
    cnt_clr     = 1'b0;
    esc_trig_o  = 1'b0;
    phase_oh    = '0;
    thresh      = timeout_cyc_i;
    fsm_error   = 1'b0;

    unique case (state_q)
      // wait for an escalation trigger or an alert trigger
      // the latter will trigger an interrupt timeout
      IdleSt: begin
        cnt_clr = 1'b1;
        esc_state_o = Idle;

        if (accu_trig_i && en_i && !clr_i) begin
          state_d    = Phase0St;
          cnt_en     = 1'b1;
          esc_trig_o = 1'b1;
        // the counter is zero in this state. so if the
        // timeout count is zero (==disabled), cnt_ge will be true.
        end else if (timeout_en_i && !cnt_ge && en_i) begin
          cnt_en  = 1'b1;
          state_d = TimeoutSt;
        end
      end
      // we are in interrupt timeout state
      // in case an escalation comes in, we immediately have to
      // switch over to the first escalation phase.
      // in case the interrupt timeout hits it's cycle count, we
      // also enter escalation phase0.
      // ongoing timeouts can always be cleared.
      TimeoutSt: begin
        esc_state_o = Timeout;

        if ((accu_trig_i && en_i && !clr_i) || (cnt_ge && timeout_en_i)) begin
          state_d    = Phase0St;
          cnt_en     = 1'b1;
          cnt_clr    = 1'b1;
          esc_trig_o = 1'b1;
        // the timeout enable is connected to the irq state
        // if that is cleared, stop the timeout counter
        end else if (timeout_en_i) begin
          cnt_en  = 1'b1;
        end else begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
        end
      end
      // note: autolocking the clear signal is done in the regfile
      Phase0St: begin
        cnt_en      = 1'b1;
        phase_oh[0] = 1'b1;
        thresh      = phase_cyc_i[0];
        esc_state_o = Phase0;

        if (clr_i) begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Phase1St;
          cnt_clr = 1'b1;
          cnt_en  = 1'b1;
        end
      end
      Phase1St: begin
        cnt_en      = 1'b1;
        phase_oh[1] = 1'b1;
        thresh      = phase_cyc_i[1];
        esc_state_o = Phase1;

        if (clr_i) begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Phase2St;
          cnt_clr = 1'b1;
          cnt_en  = 1'b1;
        end
      end
      Phase2St: begin
        cnt_en      = 1'b1;
        phase_oh[2] = 1'b1;
        thresh      = phase_cyc_i[2];
        esc_state_o = Phase2;

        if (clr_i) begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = Phase3St;
          cnt_clr = 1'b1;
        end
      end
      Phase3St: begin
        cnt_en      = 1'b1;
        phase_oh[3] = 1'b1;
        thresh      = phase_cyc_i[3];
        esc_state_o = Phase3;

        if (clr_i) begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end else if (cnt_ge) begin
          state_d = TerminalSt;
          cnt_clr = 1'b1;
          cnt_en  = 1'b0;
        end
      end
      // final, terminal state after escalation.
      // if clr is locked down, only a system reset
      // will get us out of this state
      TerminalSt: begin
        cnt_clr = 1'b1;
        esc_state_o = Terminal;
        if (clr_i) begin
          state_d = IdleSt;
        end
      end
      // error state, only reached if the FSM has been
      // glitched. in this state, we trigger all escalation
      // actions at once.
      FsmErrorSt: begin
        esc_state_o = FsmError;
        fsm_error = 1'b1;
      end
      // catch glitches.
      default: begin
        state_d = FsmErrorSt;
        esc_state_o = FsmError;
      end
    endcase

    // if any of the duplicate counter pairs has an inconsistent state
    // we move into the terminal FSM error state.
    if (accu_fail_i || cnt_check_fail) begin
      state_d = FsmErrorSt;
    end
  end

  logic [N_ESC_SEV-1:0][N_PHASES-1:0] esc_map_oh;
  for (genvar k = 0; k < N_ESC_SEV; k++) begin : gen_phase_map
    // generate configuration mask for escalation enable signals
    assign esc_map_oh[k] = N_ESC_SEV'(esc_en_i[k]) << esc_map_i[k];
    // mask reduce current phase state vector
    assign esc_sig_req_o[k] = |(esc_map_oh[k] & phase_oh) | fsm_error;
  end

  ///////////////////
  // FSM Registers //
  ///////////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(IdleSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  ////////////////
  // Assertions //
  ////////////////

  // a clear should always bring us back to idle
  `ASSERT(CheckClr_A,
      !accu_fail_i &&
      clr_i &&
      !(state_q inside {IdleSt, TimeoutSt, FsmErrorSt})
      |=>
      state_q == IdleSt)
  // if currently in idle and not enabled, must remain here
  `ASSERT(CheckEn_A,
      !accu_fail_i &&
      state_q == IdleSt &&
      !en_i
      |=>
      state_q == IdleSt)
  // Check if accumulation trigger correctly captured
  `ASSERT(CheckAccumTrig0_A,
      !accu_fail_i &&
      accu_trig_i &&
      state_q == IdleSt &&
      en_i &&
      !clr_i
      |=>
      state_q == Phase0St)
  `ASSERT(CheckAccumTrig1_A,
      !accu_fail_i &&
      accu_trig_i &&
      state_q == TimeoutSt &&
      en_i &&
      !clr_i
      |=>
      state_q == Phase0St)
  // Check if timeout correctly captured
  `ASSERT(CheckTimeout0_A,
      !accu_fail_i &&
      state_q == IdleSt &&
      timeout_en_i &&
      en_i &&
      timeout_cyc_i != 0 &&
      !accu_trig_i
      |=>
      state_q == TimeoutSt)
  `ASSERT(CheckTimeoutSt1_A,
      !accu_fail_i &&
      state_q == TimeoutSt &&
      timeout_en_i &&
      cnt_q[0] < timeout_cyc_i &&
      !accu_trig_i
      |=>
      state_q == TimeoutSt)
  `ASSERT(CheckTimeoutSt2_A,
      !accu_fail_i &&
      state_q == TimeoutSt &&
      !timeout_en_i &&
      !accu_trig_i
      |=>
      state_q == IdleSt)
  // Check if timeout correctly triggers escalation
  `ASSERT(CheckTimeoutStTrig_A,
      !accu_fail_i &&
      state_q == TimeoutSt &&
      timeout_en_i &&
      cnt_q[0] == timeout_cyc_i
      |=>
      state_q == Phase0St)
  // Check whether escalation phases are correctly switched
  `ASSERT(CheckPhase0_A,
      !accu_fail_i &&
      state_q == Phase0St &&
      !clr_i &&
      cnt_q[0] >= phase_cyc_i[0]
      |=>
      state_q == Phase1St)
  `ASSERT(CheckPhase1_A,
      !accu_fail_i &&
      state_q == Phase1St &&
      !clr_i &&
      cnt_q[0] >= phase_cyc_i[1]
      |=>
      state_q == Phase2St)
  `ASSERT(CheckPhase2_A,
      !accu_fail_i &&
      state_q == Phase2St &&
      !clr_i &&
      cnt_q[0] >= phase_cyc_i[2]
      |=>
      state_q == Phase3St)
  `ASSERT(CheckPhase3_A,
      !accu_fail_i &&
      state_q == Phase3St &&
      !clr_i &&
      cnt_q[0] >= phase_cyc_i[3]
      |=>
      state_q == TerminalSt)
  `ASSERT(AccuFailToFsmError_A,
      accu_fail_i
      |=>
      state_q == FsmErrorSt)
  `ASSERT(ErrorStIsTerminal_A,
      state_q == FsmErrorSt
      |=>
      state_q == FsmErrorSt)
  `ASSERT(ErrorStAllEscAsserted_A,
      state_q == FsmErrorSt
      |->
      esc_sig_req_o == '1)

endmodule : alert_handler_esc_timer
