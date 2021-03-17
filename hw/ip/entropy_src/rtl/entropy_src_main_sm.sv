// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src main state machine module
//
//   determines when new entropy is ready to be forwarded

module entropy_src_main_sm (
  input logic                clk_i,
  input logic                rst_ni,

  input logic                enable_i,
  input logic                ht_done_pulse_i,
  input logic                ht_fail_pulse_i,
  output logic               rst_alert_cntr_o,
  input logic                bypass_mode_i,
  output logic               rst_bypass_mode_o,
  input logic                main_stage_rdy_i,
  input logic                bypass_stage_rdy_i,
  input logic                sha3_state_vld_i,
  output logic               main_stage_pop_o,
  output logic               bypass_stage_pop_o,
  output logic               sha3_start_o,
  output logic               sha3_process_o,
  output logic               sha3_done_o,
  output logic               main_sm_err_o
);

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 9 -n 8 \
//      -s 3744885553 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||| (25.00%)
//  4: |||||||||||||||||||| (27.78%)
//  5: |||||||||||||||||||| (27.78%)
//  6: |||||||||||| (16.67%)
//  7: || (2.78%)
//  8: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 7
// Minimum Hamming weight: 3
// Maximum Hamming weight: 6
//

  localparam int StateWidth = 8;
  typedef enum logic [StateWidth-1:0] {
    Idle              = 8'b10111100, // idle
    BootHTRunning     = 8'b11100101, // boot mode, wait for health test done pulse
    BootPostHTChk     = 8'b10011010, // boot mode, wait for post health test packer not empty state
    NormHTStart       = 8'b00010011, // normal mode, pulse the sha3 start input
    NormHTRunning     = 8'b11001001, // normal mode, wait for health test done pulse
    NormSha3Process   = 8'b11010100, // normal mode, pulse the sha3 process input
    NormSha3Valid     = 8'b00101101, // normal mode, wait for sha3 valid indication
    NormSha3Done      = 8'b01111011, // normal mode, capture sha3 result, pulse done input
    Error             = 8'b01000110  // illegal state reached and hang
  } state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(Idle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d ),
    .q_o ( state_raw_q )
  );

  assign state_q = state_e'(state_raw_q);

  always_comb begin
    state_d = state_q;
    rst_bypass_mode_o = 1'b0;
    rst_alert_cntr_o = 1'b0;
    main_stage_pop_o = 1'b0;
    bypass_stage_pop_o = 1'b0;
    sha3_start_o = 1'b0;
    sha3_process_o = 1'b0;
    sha3_done_o = 1'b0;
    main_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        if (enable_i) begin
          if (bypass_mode_i) begin
            state_d = BootHTRunning;
          end else begin
            state_d = NormHTStart;
          end
        end
      end
      BootHTRunning: begin
        if (ht_done_pulse_i) begin
          if (ht_fail_pulse_i) begin
            state_d = Idle;
          end else begin
            state_d = BootPostHTChk;
          end
        end
      end
      BootPostHTChk: begin
        if (!bypass_stage_rdy_i) begin
        end else begin
          rst_alert_cntr_o = 1'b1;
          rst_bypass_mode_o = 1'b1;
          bypass_stage_pop_o = 1'b1;
          state_d = Idle;
        end
      end
      NormHTStart: begin
        sha3_start_o = 1'b1;
        state_d = NormHTRunning;
      end
      NormHTRunning: begin
        if (ht_done_pulse_i) begin
          if (ht_fail_pulse_i) begin
            sha3_done_o = 1'b1;
            state_d = Idle;
          end else begin
            state_d = NormSha3Process;
          end
        end
      end
      NormSha3Process: begin
        rst_alert_cntr_o = 1'b1;
        sha3_process_o = 1'b1;
        state_d = NormSha3Valid;
      end
      NormSha3Valid: begin
        if (sha3_state_vld_i) begin
          state_d = NormSha3Done;
        end
      end
      NormSha3Done: begin
        if (main_stage_rdy_i) begin
          sha3_done_o = 1'b1;
          main_stage_pop_o = 1'b1;
          state_d = Idle;
        end
      end
      Error: begin
        main_sm_err_o = 1'b1;
      end
      default: state_d = Error;
    endcase
  end

endmodule
