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
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte)
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic                     start_i,
  input  logic [ImemAddrWidth-1:0] start_addr_i,

  output logic                     controller_start_o,
  output logic [ImemAddrWidth-1:0] controller_start_addr_o,

  input  logic                     controller_done_i,

  output logic urnd_reseed_req_o,
  input  logic urnd_reseed_busy_i,
  output logic urnd_advance_o,

  output logic ispr_init_o
);
  otbn_start_stop_state_e state_q, state_d;

  logic [ImemAddrWidth-1:0] start_addr_q;
  logic start_addr_en;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= OtbnStartStopStateHalt;
    end else begin
      state_q <= state_d;
    end
  end

  always_ff @(posedge clk_i) begin
    if (start_addr_en) begin
      start_addr_q <= start_addr_i;
    end
  end

  always_comb begin
    urnd_reseed_req_o  = 1'b0;
    urnd_advance_o     = 1'b0;
    start_addr_en      = 1'b0;
    state_d            = state_q;
    ispr_init_o        = 1'b0;

    unique case(state_q)
      OtbnStartStopStateHalt: begin
        if (start_i) begin
          start_addr_en     = 1'b1;
          urnd_reseed_req_o = 1'b1;
          ispr_init_o       = 1'b1;
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

  assign controller_start_addr_o = start_addr_q;
endmodule
