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

  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    IDLE = 6'b000010, // idle (hamming distance = 3)
    HTDP = 6'b101110, // wait for health test done pulse
    PNMT = 6'b010100, // wait for post health test packer not empty state
    MODE = 6'b011011, // determine what mode the flow is in
    BYPS = 6'b101001, // in bypass mode
    NORM = 6'b110111  // in normal mode
  } state_e;

  state_e state_q, state_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      state_q    <= IDLE;
    end else begin
      state_q    <= state_d;
    end

  always_comb begin
    state_d = state_q;
    rst_bypass_mode_o = 1'b0;
    rst_alert_cntr_o = 1'b0;
    main_stage_pop_o = 1'b0;
    bypass_stage_pop_o = 1'b0;
    unique case (state_q)
      IDLE: begin
        if (enable_i) begin
          state_d = HTDP;
        end
      end
      HTDP: begin
        if (ht_done_pulse_i) begin
          if (ht_fail_pulse_i) begin
            state_d = IDLE;
          end else begin
            state_d = PNMT;
          end
        end
      end
      PNMT: begin
        rst_alert_cntr_o = 1'b1;
        if (postht_not_empty_i) begin
          state_d = MODE;
        end
      end
      MODE: begin
        if (bypass_mode_i) begin
          state_d = BYPS;
        end else begin
          state_d = NORM;
        end
      end
      BYPS: begin
        if (bypass_stage_rdy_i) begin
          rst_bypass_mode_o = 1'b1;
          bypass_stage_pop_o = 1'b1;
          state_d = IDLE;
        end
      end
      NORM: begin
        if (main_stage_rdy_i) begin
          main_stage_pop_o = 1'b1;
          state_d = IDLE;
        end
      end
      default: state_d = IDLE;
    endcase
  end

endmodule
