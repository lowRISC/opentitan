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
  output logic pwrup_cause_toggle_o,
  output pwrup_cause_e pwrup_cause_o,
  input ack_pwrup_i,
  input req_pwrdn_i,
  output logic ack_pwrdn_o,

  // low power entry configuration
  input main_pd_ni,
  input io_clk_en_i,
  input core_clk_en_i,
  input usb_clk_en_lp_i,
  input usb_clk_en_active_i,

  // AST interface
  input pwr_ast_rsp_t ast_i,
  output pwr_ast_req_t ast_o
);

  slow_pwr_state_e state_q, state_d;

  // All signals crossing over to other domain must be flopped
  pwrup_cause_e cause_q, cause_d;
  logic cause_toggle_q, cause_toggle_d;
  logic req_pwrup_q, req_pwrup_d;
  logic ack_pwrdn_q, ack_pwrdn_d;

  // All power signals and signals going to analog logic are flopped to avoid transitional glitches
  logic pd_nq, pd_nd;
  logic pwr_clamp_q, pwr_clamp_d;
  logic core_clk_en_q, core_clk_en_d;
  logic io_clk_en_q, io_clk_en_d;
  logic usb_clk_en_q, usb_clk_en_d;

  logic all_clks_valid;
  logic all_clks_invalid;

  // all clocks sources are valid
  // if clocks (usb) not configured to be active, then just bypass check
  assign all_clks_valid = ast_i.core_clk_val &
                          ast_i.io_clk_val &
                          (~usb_clk_en_active_i | ast_i.usb_clk_val);

  // if clocks were configured to turn off, make sure val is invalid
  // if clocks were not configured to turn off, just bypass the check
  assign all_clks_invalid = (core_clk_en_i | ~ast_i.core_clk_val) &
                            (io_clk_en_i | ~ast_i.io_clk_val) &
                            (usb_clk_en_lp_i | ~ast_i.usb_clk_val);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q        <= SlowPwrStateReset;
      cause_q        <= Por;
      cause_toggle_q <= 1'b0;
      // pwrmgr resets assuming main power domain is already ready
      pd_nq          <= 1'b1;
      pwr_clamp_q    <= 1'b0;
      core_clk_en_q  <= 1'b0;
      io_clk_en_q    <= 1'b0;
      usb_clk_en_q   <= 1'b0;
      req_pwrup_q    <= 1'b0;
      ack_pwrdn_q    <= 1'b0;
    end else begin
      state_q        <= state_d;
      cause_q        <= cause_d;
      cause_toggle_q <= cause_toggle_d;
      pd_nq          <= pd_nd;
      pwr_clamp_q    <= pwr_clamp_d;
      core_clk_en_q  <= core_clk_en_d;
      io_clk_en_q    <= io_clk_en_d;
      usb_clk_en_q   <= usb_clk_en_d;
      req_pwrup_q    <= req_pwrup_d;
      ack_pwrdn_q    <= ack_pwrdn_d;
    end
  end

  always_comb begin
    state_d        = state_q;
    cause_d        = cause_q;
    pd_nd          = pd_nq;
    cause_toggle_d = cause_toggle_q;
    pwr_clamp_d    = pwr_clamp_q;
    core_clk_en_d  = core_clk_en_q;
    io_clk_en_d    = io_clk_en_q;
    usb_clk_en_d   = usb_clk_en_q;

    req_pwrup_d    = req_pwrup_q;
    ack_pwrdn_d    = ack_pwrdn_q;

    unique case(state_q)

      SlowPwrStateReset: begin
        state_d = SlowPwrStateMainPowerOn;
        cause_d = Por;
      end

      SlowPwrStateLowPower: begin
        // reset request behaves identically to a wakeup, other than the power-up cause being
        // different
        if (wakeup_i || reset_req_i) begin
          state_d = SlowPwrStateMainPowerOn;
          cause_toggle_d = ~cause_toggle_q;
          cause_d = reset_req_i ? Reset : Wake;
        end
      end

      SlowPwrStateMainPowerOn: begin
        pd_nd = 1'b1;

        if (ast_i.main_pok) begin
          pwr_clamp_d = 1'b0;
          state_d = SlowPwrStateClocksOn;
        end
      end

      SlowPwrStateClocksOn: begin
        core_clk_en_d = 1'b1;
        io_clk_en_d = 1'b1;
        usb_clk_en_d = usb_clk_en_active_i;

        if (all_clks_valid) begin
          state_d = SlowPwrStateReqPwrUp;
        end
      end

      SlowPwrStateReqPwrUp: begin
        req_pwrup_d = 1'b1;

        // req_pwrdn_i should be 0 here to indicate
        // the request from the previous round has definitely completed
        if (ack_pwrup_i && !req_pwrdn_i) begin
          req_pwrup_d = 1'b0;
          state_d = SlowPwrStateIdle;
        end
      end

      SlowPwrStateIdle: begin
        // ack_pwrup_i should be 0 here to indicate
        // the ack from the previous round has definitively completed
        usb_clk_en_d = usb_clk_en_active_i;

        if (req_pwrdn_i && !ack_pwrup_i) begin
          state_d = SlowPwrStateAckPwrDn;
        end
      end

      SlowPwrStateAckPwrDn: begin
        ack_pwrdn_d = 1'b1;

        if (!req_pwrdn_i) begin
          ack_pwrdn_d = 1'b0;
          state_d = SlowPwrStateClocksOff;
        end
      end

      SlowPwrStateClocksOff: begin
        core_clk_en_d = core_clk_en_i;
        io_clk_en_d = io_clk_en_i;
        usb_clk_en_d = usb_clk_en_lp_i;

        if (all_clks_invalid) begin
          // if main power is turned off, assert clamp ahead
          pwr_clamp_d = ~main_pd_ni;
          state_d = SlowPwrStateMainPowerOff;
        end
      end

      SlowPwrStateMainPowerOff: begin
        pd_nd = main_pd_ni;

        // if power is never turned off, proceed directly to low power state
        if (!ast_i.main_pok | main_pd_ni) begin
          state_d = SlowPwrStateLowPower;
        end
      end

      // Very terminal state, kill everything
      default: begin
        pd_nd         = 1'b0;
        pwr_clamp_d   = 1'b1;
        core_clk_en_d = 1'b0;
        io_clk_en_d   = 1'b0;
        usb_clk_en_d  = 1'b0;
      end


    endcase // unique case (state_q)
  end // always_comb


  assign pwrup_cause_o = cause_q;
  assign pwrup_cause_toggle_o = cause_toggle_q;
  assign req_pwrup_o = req_pwrup_q;
  assign ack_pwrdn_o = ack_pwrdn_q;

  assign ast_o.core_clk_en = core_clk_en_q;
  assign ast_o.io_clk_en = io_clk_en_q;
  assign ast_o.usb_clk_en = usb_clk_en_q;
  assign ast_o.main_pd_n = pd_nq;
  assign ast_o.pwr_clamp = pwr_clamp_q;

  // This is hardwired to 1 all the time
  assign ast_o.slow_clk_en = 1'b1;


  ////////////////////////////
  ///  Unused
  ////////////////////////////

  logic unused_slow_clk_val;
  assign unused_slow_clk_val = ast_i.slow_clk_val;


endmodule
