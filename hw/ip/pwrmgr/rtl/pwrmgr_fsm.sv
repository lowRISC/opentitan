// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Fast FSM
//

`include "prim_assert.sv"

module pwrmgr_fsm
import pwrmgr_pkg::*;
(
    input clk_i,
    input rst_ni,

    // interface with slow_fsm
    input                req_pwrup_i,
    input  pwrup_cause_e pwrup_cause_i,
    output logic         ack_pwrup_o,
    output logic         req_pwrdn_o,
    input                ack_pwrdn_i,
    input                low_power_entry_i,
    input                main_pd_ni,
    input                reset_req_i,

    // consumed in pwrmgr
    output logic wkup_o,  // generate wake interrupt
    output logic wkup_record_o,  // enable wakeup recording
    output logic fall_through_o,
    output logic abort_o,
    output logic clr_hint_o,
    output logic clr_cfg_lock_o,

    // rstmgr
    output pwr_rst_req_t pwr_rst_o,
    input  pwr_rst_rsp_t pwr_rst_i,

    // clkmgr
    output logic ips_clk_en_o,

    // otp
    output logic otp_init_o,
    input        otp_done_i,
    input        otp_idle_i,

    // lc
    output logic lc_init_o,
    input        lc_done_i,
    input        lc_idle_i,

    // flash
    input flash_idle_i
);

  // state enum
  typedef enum logic [4:0] {
    StLowPower,
    StEnableClocks,
    StReleaseLcRst,
    StOtpInit,
    StLcInit,
    StAckPwrUp,
    StActive,
    StDisClks,
    StFallThrough,
    StNvmIdleChk,
    StLowPowerPrep,
    StNvmShutDown,
    StResetPrep,
    StReqPwrDn
  } state_e;

  // The code below always assumes the always on domain is index 0
  `ASSERT_INIT(AlwaysOnIndex_A, ALWAYS_ON_DOMAIN == 0)

  // when there are multiple on domains, the latter 1 should become another parameter
  localparam int OffDomainSelStart = ALWAYS_ON_DOMAIN + 1;

  // all powered down domains have resets asserted
  logic pd_n_rsts_asserted;

  // all domains have resets asserted
  logic all_rsts_asserted;

  // resets are valid
  logic reset_valid;

  // reset hint to rstmgr
  reset_cause_e reset_cause_q, reset_cause_d;

  state_e state_d, state_q;
  logic reset_ongoing_q, reset_ongoing_d;
  logic req_pwrdn_q, req_pwrdn_d;
  logic ack_pwrup_q, ack_pwrup_d;
  logic ip_clk_en_q, ip_clk_en_d;
  logic [PowerDomains-1:0] rst_lc_req_q, rst_sys_req_q;
  logic [PowerDomains-1:0] rst_lc_req_d, rst_sys_req_d;
  logic otp_init;
  logic lc_init;

  assign pd_n_rsts_asserted = pwr_rst_i.rst_lc_src_n[PowerDomains - 1:1] == '0 &
      pwr_rst_i.rst_sys_src_n[PowerDomains - 1:1] == '0;

  assign all_rsts_asserted = pwr_rst_i.rst_lc_src_n == '0 & pwr_rst_i.rst_sys_src_n == '0;

  // when in low power path, resets are controlled by domain power down
  // when in reset path, all resets must be asserted
  // when the reset cause is something else, it is invalid
  assign reset_valid = reset_cause_q == LowPwrEntry ? main_pd_ni | pd_n_rsts_asserted :
      reset_cause_q == HwReq ? all_rsts_asserted : 1'b0;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StLowPower;
      ack_pwrup_q <= 1'b0;
      req_pwrdn_q <= 1'b0;
      reset_ongoing_q <= 1'b0;
      ip_clk_en_q <= 1'b0;
      rst_lc_req_q <= {PowerDomains{1'b1}};
      rst_sys_req_q <= {PowerDomains{1'b1}};
      reset_cause_q <= ResetUndefined;
    end else begin
      state_q <= state_d;
      ack_pwrup_q <= ack_pwrup_d;
      req_pwrdn_q <= req_pwrdn_d;
      reset_ongoing_q <= reset_ongoing_d;
      ip_clk_en_q <= ip_clk_en_d;
      rst_lc_req_q <= rst_lc_req_d;
      rst_sys_req_q <= rst_sys_req_d;
      reset_cause_q <= reset_cause_d;
    end
  end

  always_comb begin
    otp_init = 1'b0;
    lc_init = 1'b0;
    wkup_o = 1'b0;
    wkup_record_o = 1'b0;
    fall_through_o = 1'b0;
    abort_o = 1'b0;
    clr_hint_o = 1'b0;
    clr_cfg_lock_o = 1'b0;

    state_d = state_q;
    ack_pwrup_d = ack_pwrup_q;
    req_pwrdn_d = req_pwrdn_q;
    reset_ongoing_d = reset_ongoing_q;
    ip_clk_en_d = ip_clk_en_q;
    rst_lc_req_d = rst_lc_req_q;
    rst_sys_req_d = rst_sys_req_q;
    reset_cause_d = reset_cause_q;

    unique case (state_q)

      StLowPower: begin
        if (req_pwrup_i || reset_ongoing_q) begin
          state_d = StEnableClocks;
        end
      end

      StEnableClocks: begin
        ip_clk_en_d = 1'b1;

        if (1'b1) begin  // TODO, add a feedback signal to check clocks are enabled
          state_d = StReleaseLcRst;
        end
      end

      StReleaseLcRst: begin
        rst_lc_req_d = '0;  // release rst_lc_n for all power domains

        if (&pwr_rst_i.rst_lc_src_n) begin  // once all resets are released
          state_d = StOtpInit;
        end
      end

      StOtpInit: begin
        otp_init = 1'b1;

        if (otp_done_i) begin
          state_d = StLcInit;
        end
      end

      StLcInit: begin
        lc_init = 1'b1;

        if (lc_done_i) begin
          state_d = StAckPwrUp;


        end
      end

      StAckPwrUp: begin
        // only ack the slow_fsm if we actually transitioned through it
        ack_pwrup_d = !reset_ongoing_q;

        // wait for request power up to drop relative to ack
        if (!req_pwrup_i || reset_ongoing_q) begin
          ack_pwrup_d = 1'b0;
          clr_cfg_lock_o = 1'b1;
          wkup_o = pwrup_cause_i == Wake;
          state_d = StActive;
        end
      end

      StActive: begin
        rst_sys_req_d = '0;
        reset_cause_d = ResetNone;

        if (reset_req_i || low_power_entry_i) begin
          reset_cause_d = ResetUndefined;
          state_d = StDisClks;
        end
      end

      StDisClks: begin
        ip_clk_en_d = 1'b0;

        if (1'b1) begin  // TODO, add something to check that clocks are disabled
          state_d = reset_req_i ? StNvmShutDown : StFallThrough;
          wkup_record_o = !reset_req_i;
        end
      end

      // Low Power Path
      StFallThrough: begin
        clr_hint_o = 1'b1;

        // the processor was interrupted after it asserted WFI and is executing again
        if (!low_power_entry_i) begin
          ip_clk_en_d = 1'b1;
          wkup_o = 1'b1;
          fall_through_o = 1'b1;
          state_d = StActive;
        end else begin
          state_d = StNvmIdleChk;
        end
      end

      StNvmIdleChk: begin

        if (otp_idle_i && lc_idle_i && flash_idle_i) begin
          state_d = StLowPowerPrep;
        end else begin
          ip_clk_en_d = 1'b1;
          wkup_o = 1'b1;
          abort_o = 1'b1;
          state_d = StActive;
        end
      end

      StLowPowerPrep: begin
        reset_cause_d = LowPwrEntry;

        // reset non-always-on domains if requested
        // this includes the clock manager, which implies pwr/rst managers must
        // be fed directly from the source
        for (int i = OffDomainSelStart; i < PowerDomains; i++) begin
          rst_lc_req_d[i] = ~main_pd_ni;
          rst_sys_req_d[i] = ~main_pd_ni;
        end

        if (reset_valid) begin
          state_d = StReqPwrDn;
        end
      end

      StReqPwrDn: begin
        req_pwrdn_d = 1'b1;

        if (ack_pwrdn_i) begin
          req_pwrdn_d = 1'b0;
          state_d = StLowPower;
        end
      end

      // Reset Path
      // This state is TODO, the details are still under discussion
      StNvmShutDown: begin
        clr_hint_o = 1'b1;
        reset_ongoing_d = 1'b1;
        state_d = StResetPrep;
      end

      StResetPrep: begin
        reset_cause_d = HwReq;
        rst_lc_req_d = {PowerDomains{1'b1}};
        rst_sys_req_d = {PowerDomains{1'b1}};

        if (reset_valid) begin
          state_d = StLowPower;
        end
      end

      // Terminal state, kill everything
      default: begin
        rst_lc_req_d = {PowerDomains{1'b1}};
        rst_sys_req_d = {PowerDomains{1'b1}};
        ip_clk_en_d = 1'b0;
      end

    endcase  // unique case (state_q)
  end  // always_comb

  assign ack_pwrup_o = ack_pwrup_q;
  assign req_pwrdn_o = req_pwrdn_q;

  assign pwr_rst_o.rst_lc_req = rst_lc_req_q;
  assign pwr_rst_o.rst_sys_req = rst_sys_req_q;
  assign pwr_rst_o.reset_cause = reset_cause_q;

  assign otp_init_o = otp_init;
  assign lc_init_o = lc_init;
  assign ips_clk_en_o = ip_clk_en_q;


endmodule
