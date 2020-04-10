// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Slow FSM
//

`include "prim_assert.sv"

module pwrmgr_slow_fsm import pwrmgr_pkg::*; (
  input clk_i,
  input rst_ni,

  // sync'ed requests from peripherals
  input wakeup_i,
  input reset_req_i,

  // interface with fast fsm
  output logic req_pwrup_o,
  output pwrup_cause_e pwrup_cause_o,
  input ack_pwrup_i,
  input req_pwrdn_i,
  output logic ack_pwrdn_o,

  // low power entry configuration
  input main_pdb_i,
  input io_clk_en_i,
  input core_clk_en_i,

  // AST interface
  input pwr_ast_rsp_t ast_i,
  output pwr_ast_req_t ast_o
);

  // state enum
  typedef enum logic [3:0] {
    StReset,
    StLowPower,
    StMainPowerOn,
    StClocksOn,
    StReqPwrUp,
    StIdle,
    StAckPwrDn,
    StClocksOff,
    StMainPowerOff
  } state_e;

  state_e state_q, state_d;
  pwrup_cause_e cause_q, cause_d;

  // All power signals and signals going to analog logic are flopped to avoid transitioanl glitches
  logic pdb_q, pdb_d;
  logic pwr_clamp_q, pwr_clamp_d;
  logic core_clk_en_q, core_clk_en_d;
  logic io_clk_en_q, io_clk_en_d;

  logic all_clks_valid;
  logic all_clks_invalid;

  assign all_clks_valid = ast_i.core_clk_val == 2'b10 && ast_i.io_clk_val == 2'b10;

  // if clock were configured to turn off, make sure val is 2'b01
  assign all_clks_invalid = (core_clk_en_i | ast_i.core_clk_val == 2'b01) &&
                            (io_clk_en_i   | ast_i.io_clk_val == 2'b01);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q       <= StReset;
      cause_q       <= Por;
      pdb_q         <= 1'b0;
      pwr_clamp_q   <= 1'b1;
      core_clk_en_q <= 1'b0;
      io_clk_en_q   <= 1'b0;
    end else begin
      state_q       <= state_d;
      cause_q       <= cause_d;
      pdb_q         <= pdb_d;
      pwr_clamp_q   <= pwr_clamp_d;
      core_clk_en_q <= core_clk_en_d;
      io_clk_en_q   <= io_clk_en_d;
    end
  end

  always_comb begin
    state_d       = state_q;
    cause_d       = cause_q;
    pdb_d         = pdb_q;
    pwr_clamp_d   = pwr_clamp_q;
    core_clk_en_d = core_clk_en_q;
    io_clk_en_d   = io_clk_en_q;

    req_pwrup_o   = 1'b0;
    ack_pwrdn_o   = 1'b0;

    unique case(state_q)

      StReset: begin
        state_d = StMainPowerOn;
        cause_d = Por;
      end

      StLowPower: begin
        // reset request behaves identically to a wakeup, other than the power-up cause being
        // different
        if (wakeup_i || reset_req_i) begin
          state_d = StMainPowerOn;
          cause_d = reset_req_i ? Reset : Wake;
        end
      end

      StMainPowerOn: begin
        pdb_d = 1'b1;

        if (ast_i.main_pok) begin
          pwr_clamp_d = 1'b0;
          state_d = StClocksOn;
        end
      end

      StClocksOn: begin
        core_clk_en_d = 1'b1;
        io_clk_en_d = 1'b1;

        if (all_clks_valid) begin
          state_d = StReqPwrUp;
        end
      end

      StReqPwrUp: begin
        req_pwrup_o = 1'b1;

        if (ack_pwrup_i) begin
          state_d = StIdle;

        end
      end

      StIdle: begin
        if (req_pwrdn_i) begin
          state_d = StAckPwrDn;
        end
      end

      StAckPwrDn: begin
        ack_pwrdn_o = 1'b1;

        if (!req_pwrdn_i) begin
          state_d = StClocksOff;
        end
      end

      StClocksOff: begin
        core_clk_en_d = core_clk_en_i;
        io_clk_en_d = io_clk_en_i;

        if (all_clks_invalid) begin
          // if main power is turned off, assert clamp ahead
          pwr_clamp_d = ~main_pdb_i;
          state_d = StMainPowerOff;
        end
      end

      StMainPowerOff: begin
        pdb_d = main_pdb_i;

        // if power is never turned off, proceed directly to low power state
        if (!ast_i.main_pok | main_pdb_i) begin
          state_d = StLowPower;
        end
      end

      // Very terminal state, kill everything
      default: begin
        pdb_d         = 1'b0;
        pwr_clamp_d   = 1'b1;
        core_clk_en_d = 1'b0;
        io_clk_en_d   = 1'b0;
      end


    endcase // unique case (state_q)
  end // always_comb


  assign pwrup_cause_o = cause_q;

  assign ast_o.core_clk_en = core_clk_en_q;
  assign ast_o.io_clk_en = io_clk_en_q;
  assign ast_o.main_pdb = pdb_q;
  assign ast_o.pwr_clamp = pwr_clamp_q;

  // This is hardwired to 1 all the time
  assign ast_o.slow_clk_en = 1'b1;


  ////////////////////////////
  ///  Unused
  ////////////////////////////

  logic [1:0] unused_slow_clk_val;
  assign unused_slow_clk_val = ast_i.slow_clk_val;


endmodule
