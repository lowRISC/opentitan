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
  input logic                postht_not_empty_i,
  output logic               rst_alert_cntr_o,
  input logic                bypass_mode_i,
  output logic               rst_bypass_mode_o,
  input logic                main_stage_rdy_i,
  input logic                bypass_stage_rdy_i,
  output logic               main_stage_pop_o,
  output logic               bypass_stage_pop_o
);

  // Encoding generated with ./sparse-fsm-encode.py -d 3 -m 6 -n 8 -s 3348095039
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: |||||| (13.33%)
  // 4: |||||||||||||||| (33.33%)
  // 5: |||||||||||||||||||| (40.00%)
  // 6: |||||| (13.33%)
  // 7: --
  // 8: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 6
  //

  localparam int StateWidth = 8;
  typedef enum logic [StateWidth-1:0] {
    Idle              = 8'b00011111, // idle
    HealthTestDone    = 8'b01111010, // wait for health test done pulse
    PostHealthTestChk = 8'b11111001, // wait for post health test packer not empty state
    FlowModeChk       = 8'b10110100, // determine what mode the flow is in
    BypassMode        = 8'b00100011, // in bypass mode
    NormalMode        = 8'b11001000  // in normal mode
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
    unique case (state_q)
      Idle: begin
        if (enable_i) begin
          state_d = HealthTestDone;
        end
      end
      HealthTestDone: begin
        if (ht_done_pulse_i) begin
          if (ht_fail_pulse_i) begin
            state_d = Idle;
          end else begin
            state_d = PostHealthTestChk;
          end
        end
      end
      PostHealthTestChk: begin
        rst_alert_cntr_o = 1'b1;
        if (postht_not_empty_i) begin
          state_d = FlowModeChk;
        end
      end
      FlowModeChk: begin
        if (bypass_mode_i) begin
          state_d = BypassMode;
        end else begin
          state_d = NormalMode;
        end
      end
      BypassMode: begin
        if (bypass_stage_rdy_i) begin
          rst_bypass_mode_o = 1'b1;
          bypass_stage_pop_o = 1'b1;
          state_d = Idle;
        end
      end
      NormalMode: begin
        if (main_stage_rdy_i) begin
          main_stage_pop_o = 1'b1;
          state_d = Idle;
        end
      end
      default: state_d = Idle;
    endcase
  end

endmodule
