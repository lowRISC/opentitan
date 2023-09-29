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
  input rst_main_ni,

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
  output logic rst_req_o,
  output logic fsm_invalid_o,
  input clr_req_i,
  output logic usb_ip_clk_en_o,
  input usb_ip_clk_status_i,

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

  logic clk_active;

  // All power signals and signals going to analog logic are flopped to avoid transitional glitches
  logic pd_nq, pd_nd;
  logic pwr_clamp_q, pwr_clamp_d;
  logic pwr_clamp_env_q, pwr_clamp_env_d;
  logic core_clk_en_q, core_clk_en_d;
  logic io_clk_en_q, io_clk_en_d;
  logic usb_clk_en_q, usb_clk_en_d;
  logic fsm_invalid_q, fsm_invalid_d;

  logic all_clks_valid;
  logic all_clks_invalid;

  // when to monitor pok for instability
  // These are monitored only in active and low power states
  logic mon_main_pok;
  logic set_main_pok;
  logic async_main_pok_st;
  logic main_pok_st;

  // all clocks sources are valid
  // if clocks (usb) not configured to be active, then just bypass check
  assign all_clks_valid = ast_i.core_clk_val &
                          ast_i.io_clk_val &
                          (~usb_clk_en_active_i | ast_i.usb_clk_val);

  // usb clock state during low power is not completely controlled by
  // input.
  // if main_pd_ni is 0, (ie power will be turned off), then the low power
  // state of usb is also off.  If main_pd_ni is 1 (power will be kept on),
  // then the low power state of usb is directly controlled.
  logic usb_clk_en_lp;
  assign usb_clk_en_lp = main_pd_ni & usb_clk_en_lp_i;

  // all other clocks are also diasbled when power is turned off.
  logic core_clk_en;
  logic io_clk_en;
  assign core_clk_en = main_pd_ni & core_clk_en_i;
  assign io_clk_en = main_pd_ni & io_clk_en_i;

  // if clocks were configured to turn off, make sure val is invalid
  // if clocks were not configured to turn off, just bypass the check
  assign all_clks_invalid = (core_clk_en | ~ast_i.core_clk_val) &
                            (io_clk_en | ~ast_i.io_clk_val) &
                            (usb_clk_en_lp | ~ast_i.usb_clk_val);

  // ensure that clock controls are constantly re-evaluated and not just
  // in one specific state
  // When fsm is invalid, force the clocks to be on such that the fast fsm
  // can forcibly reset the system.
  // In the event the clocks cannot be turned on even when forced, the fsm
  // invalid signal forces power to turn off.
  assign core_clk_en_d = fsm_invalid_q | (clk_active | core_clk_en);
  assign io_clk_en_d   = fsm_invalid_q | (clk_active | io_clk_en);
  assign usb_clk_en_d  = fsm_invalid_q | (clk_active ? usb_clk_en_active_i : usb_clk_en_lp);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cause_q        <= Por;
      cause_toggle_q <= 1'b0;
      pd_nq          <= 1'b1;
      pwr_clamp_q    <= 1'b1;
      pwr_clamp_env_q <= 1'b1;
      core_clk_en_q  <= 1'b0;
      io_clk_en_q    <= 1'b0;
      usb_clk_en_q   <= 1'b0;
      req_pwrup_q    <= 1'b0;
      ack_pwrdn_q    <= 1'b0;
      fsm_invalid_q  <= 1'b0;
    end else begin
      cause_q        <= cause_d;
      cause_toggle_q <= cause_toggle_d;
      pd_nq          <= pd_nd;
      pwr_clamp_q    <= pwr_clamp_d;
      pwr_clamp_env_q <= pwr_clamp_env_d;
      core_clk_en_q  <= core_clk_en_d;
      io_clk_en_q    <= io_clk_en_d;
      usb_clk_en_q   <= usb_clk_en_d;
      req_pwrup_q    <= req_pwrup_d;
      ack_pwrdn_q    <= ack_pwrdn_d;
      fsm_invalid_q  <= fsm_invalid_d;
    end
  end

  // SEC_CM: FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, slow_pwr_state_e, SlowPwrStateReset)

  always_comb begin
    state_d        = state_q;
    cause_d        = cause_q;
    pd_nd          = pd_nq;
    cause_toggle_d = cause_toggle_q;
    pwr_clamp_d    = pwr_clamp_q;
    pwr_clamp_env_d = pwr_clamp_env_q;

    req_pwrup_d    = req_pwrup_q;
    ack_pwrdn_d    = ack_pwrdn_q;
    fsm_invalid_d  = fsm_invalid_q;

    set_main_pok   = '0;

    clk_active     = '0;

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

        if (main_pok_st) begin
          set_main_pok = 1'b1;
          pwr_clamp_env_d = 1'b0;
          state_d = SlowPwrStatePwrClampOff;
        end
      end

      SlowPwrStatePwrClampOff: begin
        pwr_clamp_d = 1'b0;
        state_d = SlowPwrStateClocksOn;
      end

      SlowPwrStateClocksOn: begin
        clk_active = 1'b1;

        if (all_clks_valid) begin
          state_d = SlowPwrStateReqPwrUp;
        end
      end

      SlowPwrStateReqPwrUp: begin
        clk_active = 1'b1;
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
        clk_active = 1'b1;

        if (req_pwrdn_i && !ack_pwrup_i) begin
          state_d = SlowPwrStateAckPwrDn;
        end
      end

      SlowPwrStateAckPwrDn: begin
        clk_active = 1'b1;
        ack_pwrdn_d = 1'b1;

        if (!req_pwrdn_i) begin
          ack_pwrdn_d = 1'b0;
          state_d = SlowPwrStateClocksOff;
        end
      end

      SlowPwrStateClocksOff: begin
        if (all_clks_invalid) begin
          // if main power is turned off, assert early clamp ahead
          pwr_clamp_env_d = ~main_pd_ni;
          state_d = SlowPwrStatePwrClampOn;
        end
      end

      SlowPwrStatePwrClampOn: begin
        // if main power is turned off, assert clamp ahead
        pwr_clamp_d = pwr_clamp_env_q;
        state_d = SlowPwrStateMainPowerOff;
      end

      SlowPwrStateMainPowerOff: begin
        pd_nd = main_pd_ni;

        // Proceed if power is already off, or if there was no intent to
        // turn off the power.
        if (!main_pok_st | main_pd_ni) begin
          state_d = SlowPwrStateLowPower;
        end
      end

      // Very terminal state, kill everything
      // Signal the fast FSM if it somehow is still running.
      // Both FSMs are now permanently out of sync and the device
      // must be rebooted.
      // SEC_CM: FSM.TERMINAL
      default: begin
        fsm_invalid_d = 1'b1;
        pd_nd         = 1'b0;
        pwr_clamp_d   = 1'b1;
      end
    endcase // unique case (state_q)
  end // always_comb

  // If the main_pok ever drops, capture that glitch
  // and hold onto it for reset escalation
  always_ff @(posedge clk_i or negedge rst_main_ni) begin
    if (!rst_main_ni) begin
      async_main_pok_st <= '0;
    end else begin
      async_main_pok_st <= ast_i.main_pok;
    end
  end

  // We need to synchronize the above because the reset
  // may cause the signal to change at any time.
  prim_flop_2sync # (
    .Width(1)
  ) u_main_pok_sync (
    .clk_i,
    .rst_ni,
    .d_i(async_main_pok_st),
    .q_o(main_pok_st)
  );

  // Determine when pok should be monitored
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mon_main_pok <= '0;
    end else if (!pd_nd && mon_main_pok) begin
      mon_main_pok <= 1'b0;
    end else if (set_main_pok) begin
      mon_main_pok <= 1'b1;
    end
  end

  // power stability reset request
  // If the main power becomes unstable for whatever reason,
  // request reset
  // SEC_CM: MAIN_PD.RST.LOCAL_ESC
  logic pwr_rst_req;
  assign pwr_rst_req = mon_main_pok & ~main_pok_st;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rst_req_o <= '0;
    end else if (clr_req_i) begin
      rst_req_o <= '0;
    end else begin
      rst_req_o <= rst_req_o | pwr_rst_req;
    end
  end

  assign pwrup_cause_o = cause_q;
  assign pwrup_cause_toggle_o = cause_toggle_q;
  assign req_pwrup_o = req_pwrup_q;
  assign ack_pwrdn_o = ack_pwrdn_q;
  assign fsm_invalid_o = fsm_invalid_q;

  assign ast_o.core_clk_en = core_clk_en_q;
  assign ast_o.io_clk_en = io_clk_en_q;
  // usb's enable is handshake with pwr_fsm, as it can be turned on/off
  // outside of the normal low power sequence
  prim_flop #(
    .Width(1),
    .ResetValue('0)
  ) u_usb_clk_en (
    .clk_i,
    .rst_ni,
    // immediate enable
    // graceful disable when status is 0
    .d_i(usb_clk_en_q | usb_ip_clk_status_i),
    .q_o(ast_o.usb_clk_en)
  );
  assign usb_ip_clk_en_o = usb_clk_en_q;

  assign ast_o.main_pd_n = pd_nq;
  assign ast_o.pwr_clamp_env = pwr_clamp_env_q;
  assign ast_o.pwr_clamp = pwr_clamp_q;
  // This is hardwired to 1 all the time
  assign ast_o.slow_clk_en = 1'b1;


  ////////////////////////////
  ///  Unused
  ////////////////////////////

  logic unused_slow_clk_val;
  assign unused_slow_clk_val = ast_i.slow_clk_val;

  ////////////////////////////
  ///  Assertion
  ////////////////////////////
  // Under normal circumstances, this should NEVER fire
  // May need to add a signal to disable this check for simulation
  `ASSERT(IntRstReq_A, pwr_rst_req == '0)

endmodule
