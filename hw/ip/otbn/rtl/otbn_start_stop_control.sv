// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * State machine to handle actions that occur around the start and stop of OTBN.
 *
 * This recieves the start signals from the top-level and passes them on to the
 * controller to begin execution when pre-start actions have finished.
 *
 * pre-start actions:
 *  - Seed LFSR for URND
 */

`include "prim_assert.sv"

module otbn_start_stop_control
  import otbn_pkg::*;
(
  input  logic clk_i,
  input  logic rst_ni,

  input  logic start_i,

  output logic controller_start_o,

  input  logic controller_done_i,

  output logic urnd_reseed_req_o,
  input  logic urnd_reseed_busy_i,
  output logic urnd_advance_o,

  output logic ispr_init_o,
  output logic state_reset_o
);
  otbn_start_stop_state_e state_q, state_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= OtbnStartStopStateHalt;
    end else begin
      state_q <= state_d;
    end
  end

  always_comb begin
    urnd_reseed_req_o = 1'b0;
    urnd_advance_o    = 1'b0;
    state_d           = state_q;
    ispr_init_o       = 1'b0;
    state_reset_o     = 1'b0;

    unique case(state_q)
      OtbnStartStopStateHalt: begin
        if (start_i) begin
          urnd_reseed_req_o = 1'b1;
          ispr_init_o       = 1'b1;
          state_reset_o     = 1'b1;
          state_d           = OtbnStartStopStateUrndRefresh;
        end
      end
      OtbnStartStopStateUrndRefresh: begin
        if (!urnd_reseed_busy_i) begin
          state_d     = OtbnStartStopStateRunning;
        end
      end
      OtbnStartStopStateRunning: begin
        urnd_advance_o = 1'b1;
        if (controller_done_i) begin
          state_d = OtbnStartStopStateHalt;
        end
      end
      default: ;
    endcase
  end

  // Logic separate from main FSM code to avoid false combinational loop warning from verilator
  assign controller_start_o = (state_q == OtbnStartStopStateUrndRefresh) & !urnd_reseed_busy_i;

  `ASSERT(StartStopStateValid,
      state_q inside {OtbnStartStopStateHalt,
                      OtbnStartStopStateUrndRefresh,
                      OtbnStartStopStateRunning})

endmodule
