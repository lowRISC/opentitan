// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src main state machine module
//
//   determines when new entropy is ready to be forwarded

module entropy_src_main_sm #(
  localparam int StateWidth = 9
) (
  input logic                   clk_i,
  input logic                   rst_ni,

  input logic                   enable_i,
  input logic                   ht_done_pulse_i,
  input logic                   ht_fail_pulse_i,
  input logic                   alert_thresh_fail_i,
  input logic                   sfifo_esfinal_full_i,
  output logic                  rst_alert_cntr_o,
  input logic                   bypass_mode_i,
  input logic                   main_stage_rdy_i,
  input logic                   bypass_stage_rdy_i,
  input logic                   sha3_state_vld_i,
  output logic                  main_stage_push_o,
  output logic                  bypass_stage_pop_o,
  output logic                  boot_phase_done_o,
  output logic                  sha3_start_o,
  output logic                  sha3_process_o,
  output logic                  sha3_done_o,
  output logic                  cs_aes_halt_req_o,
  input logic                   cs_aes_halt_ack_i,
  input logic                   local_escalate_i,
  output logic                  main_sm_alert_o,
  output logic                  main_sm_idle_o,
  output logic [StateWidth-1:0] main_sm_state_o,
  output logic                  main_sm_err_o
);

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 19 -n 9 \
//      -s 1097041703 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||| (19.88%)
//  4: |||||||||||||||||||| (27.49%)
//  5: |||||||||||||||||| (25.73%)
//  6: |||||||||||| (17.54%)
//  7: ||||| (7.02%)
//  8: | (2.34%)
//  9: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 8
// Minimum Hamming weight: 2
// Maximum Hamming weight: 7
//

  typedef enum logic [StateWidth-1:0] {
    Idle              = 9'b001011110, // idle
    BootHTRunning     = 9'b010101111, // boot mode, wait for health test done pulse
    BootPostHTChk     = 9'b011001101, // boot mode, wait for post health test packer not empty state
    BootPhaseDone     = 9'b101011000, // boot mode, stay here until master enable is off
    StartupHTStart    = 9'b000111011, // startup mode, pulse the sha3 start input
    StartupPhase1     = 9'b010111000, // startup mode, look for first test pass/fail
    StartupPass1      = 9'b000010101, // startup mode, look for first test pass/fail, done if pass
    StartupFail1      = 9'b001100100, // startup mode, look for second fail, alert if fail
    ContHTStart       = 9'b111010011, // continuous test mode, pulse the sha3 start input
    ContHTRunning     = 9'b100101000, // continuous test mode, wait for health test done pulse
    Sha3MsgDone       = 9'b000100001, // sha3 mode, all input messages added, ready to process
    Sha3Prep          = 9'b011100010, // sha3 mode, request csrng arb to reduce power
    Sha3Process       = 9'b101001111, // sha3 mode, pulse the sha3 process input
    Sha3Valid         = 9'b110111110, // sha3 mode, wait for sha3 valid indication
    Sha3Done          = 9'b011010000, // sha3 mode, capture sha3 result, pulse done input
    Sha3Quiesce       = 9'b110010100, // sha3 mode, goto alert state or continuous check mode
    AlertState        = 9'b110100011, // if some alert condition occurs, pulse an alert indication
    AlertHang         = 9'b100010010, // after pulsing alert signal, hang here until sw handles
    Error             = 9'b100100110  // illegal state reached and hang
  } state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.

  prim_sparse_fsm_flop #(
    .StateEnumT(state_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(Idle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d ),
    .state_o ( state_raw_q )
  );

  assign state_q = state_e'(state_raw_q);
  assign main_sm_state_o = state_raw_q;

  always_comb begin
    state_d = state_q;
    rst_alert_cntr_o = 1'b0;
    main_stage_push_o = 1'b0;
    bypass_stage_pop_o = 1'b0;
    boot_phase_done_o = 1'b0;
    sha3_start_o = 1'b0;
    sha3_process_o = 1'b0;
    sha3_done_o = 1'b0;
    cs_aes_halt_req_o = 1'b0;
    main_sm_alert_o = 1'b0;
    main_sm_idle_o = 1'b0;
    main_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        main_sm_idle_o = 1'b1;
        if (enable_i) begin
          if (bypass_mode_i) begin
            state_d = BootHTRunning;
          end else begin
            state_d = StartupHTStart;
          end
        end
      end
      BootHTRunning: begin
        if (!enable_i) begin
          state_d = Idle;
        end else if (bypass_stage_rdy_i) begin
          // pop if prior ht phase failed
          bypass_stage_pop_o = 1'b1;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              if (alert_thresh_fail_i) begin
                state_d = AlertState;
              end else begin
                state_d = Idle;
              end
            end else begin
              state_d = BootPostHTChk;
            end
          end
        end
      end
      BootPostHTChk: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (!bypass_stage_rdy_i) begin
          end else begin
            rst_alert_cntr_o = 1'b1;
            bypass_stage_pop_o = 1'b1;
            main_stage_push_o = 1'b1;
            state_d = BootPhaseDone;
          end
        end
      end
      BootPhaseDone: begin
        boot_phase_done_o = 1'b1;
        if (!enable_i) begin
          state_d = Idle;
        end
      end
      StartupHTStart: begin
        if (!enable_i || sfifo_esfinal_full_i) begin
          state_d = Idle;
        end else begin
          sha3_start_o = 1'b1;
          state_d = StartupPhase1;
        end
      end
      StartupPhase1: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              state_d = StartupFail1;
            end else begin
              state_d = StartupPass1;
            end
          end
        end
      end
      StartupPass1: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              state_d = StartupFail1;
            end else begin
              // Passed two consecutive tests
              state_d = Sha3MsgDone;
            end
          end
        end
      end
      StartupFail1: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (ht_done_pulse_i) begin
            if (ht_fail_pulse_i) begin
              // Failed two consecutive tests
              state_d = AlertState;
            end else begin
              state_d = StartupPass1;
            end
          end
        end
      end
      ContHTStart: begin
        if (!enable_i || sfifo_esfinal_full_i) begin
          state_d = Idle;
        end else begin
          sha3_start_o = 1'b1;
          state_d = ContHTRunning;
        end
      end
      ContHTRunning: begin
        // pass or fail of HT is the same path
        if (ht_done_pulse_i || !enable_i) begin
          state_d = Sha3MsgDone;
        end
      end
      Sha3MsgDone: begin
        state_d = Sha3Prep;
      end
      Sha3Prep: begin
        // for normal or halt cases, always prevent a power spike
        cs_aes_halt_req_o = 1'b1;
        if (cs_aes_halt_ack_i) begin
          state_d = Sha3Process;
        end
      end
      Sha3Process: begin
        cs_aes_halt_req_o = 1'b1;
        rst_alert_cntr_o = 1'b1;
        sha3_process_o = 1'b1;
        state_d = Sha3Valid;
      end
      Sha3Valid: begin
        cs_aes_halt_req_o = 1'b1;
        if (sha3_state_vld_i) begin
          state_d = Sha3Done;
        end
      end
      Sha3Done: begin
        if (!enable_i) begin
          sha3_done_o = 1'b1;
          state_d = Idle;
        end else begin
          if (main_stage_rdy_i) begin
            sha3_done_o = 1'b1;
            main_stage_push_o = 1'b1;
            state_d = Sha3Quiesce;
          end
        end
      end
      Sha3Quiesce: begin
        if (!enable_i) begin
          state_d = Idle;
        end else if (alert_thresh_fail_i) begin
          state_d = AlertState;
        end else begin
          state_d = ContHTStart;
        end
      end
      AlertState: begin
        main_sm_alert_o = 1'b1;
        state_d = AlertHang;
      end
      AlertHang: begin
        if (!enable_i) begin
          state_d = Idle;
        end
      end
      Error: begin
        main_sm_err_o = 1'b1;
      end
      default: state_d = Error;
    endcase
    if (local_escalate_i) begin
      state_d = Error;
    end
  end

endmodule
