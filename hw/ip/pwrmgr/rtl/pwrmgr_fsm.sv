// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Fast FSM
//

`include "prim_assert.sv"

module pwrmgr_fsm import pwrmgr_pkg::*; import pwrmgr_reg_pkg::*;(
  input clk_i,
  input rst_ni,

  // interface with slow_fsm
  input req_pwrup_i,
  input pwrup_cause_e pwrup_cause_i,
  output logic ack_pwrup_o,
  output logic req_pwrdn_o,
  input ack_pwrdn_i,
  input low_power_entry_i,
  input main_pd_ni,
  input [NumRstReqs:0] reset_reqs_i,

  // consumed in pwrmgr
  output logic wkup_o,        // generate wake interrupt
  output logic wkup_record_o, // enable wakeup recording
  output logic fall_through_o,
  output logic abort_o,
  output logic clr_hint_o,
  output logic clr_cfg_lock_o,

  // rstmgr
  output pwr_rst_req_t pwr_rst_o,
  input pwr_rst_rsp_t pwr_rst_i,

  // clkmgr
  output logic ips_clk_en_o,
  input clk_en_status_i,

  // otp
  output logic otp_init_o,
  input otp_done_i,
  input otp_idle_i,

  // lc
  output logic lc_init_o,
  input lc_done_i,
  input lc_idle_i,

  // flash
  output logic flash_init_o,
  input flash_done_i,
  input flash_idle_i
);

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

  // reset request
  logic reset_req;

  fast_pwr_state_e state_d, state_q;
  logic reset_ongoing_q, reset_ongoing_d;
  logic req_pwrdn_q, req_pwrdn_d;
  logic ack_pwrup_q, ack_pwrup_d;
  logic ip_clk_en_q, ip_clk_en_d;
  logic [PowerDomains-1:0] rst_lc_req_q, rst_sys_req_q;
  logic [PowerDomains-1:0] rst_lc_req_d, rst_sys_req_d;
  logic otp_init;
  logic lc_init;
  logic flash_init_d;

  assign pd_n_rsts_asserted = pwr_rst_i.rst_lc_src_n[PowerDomains-1:1] == '0 &
                              pwr_rst_i.rst_sys_src_n[PowerDomains-1:1] == '0;

  assign all_rsts_asserted = pwr_rst_i.rst_lc_src_n == '0 &
                             pwr_rst_i.rst_sys_src_n == '0;

  assign reset_req = |reset_reqs_i;

  // when in low power path, resets are controlled by domain power down
  // when in reset path, all resets must be asserted
  // when the reset cause is something else, it is invalid
  assign reset_valid = reset_cause_q == LowPwrEntry ? main_pd_ni | pd_n_rsts_asserted :
                       reset_cause_q == HwReq       ? all_rsts_asserted : 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= FastPwrStateLowPower;
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
    flash_init_d = 1'b0;

    unique case(state_q)

      FastPwrStateLowPower: begin
        if (req_pwrup_i || reset_ongoing_q) begin
          state_d = FastPwrStateEnableClocks;
        end
      end

      FastPwrStateEnableClocks: begin
        ip_clk_en_d = 1'b1;

        if (clk_en_status_i) begin
          state_d = FastPwrStateReleaseLcRst;
        end
      end

      FastPwrStateReleaseLcRst: begin
        rst_lc_req_d = '0;  // release rst_lc_n for all power domains

        if (&pwr_rst_i.rst_lc_src_n) begin // once all resets are released
          state_d = FastPwrStateOtpInit;
        end
      end

      FastPwrStateOtpInit: begin
        otp_init = 1'b1;

        if (otp_done_i) begin
          state_d = FastPwrStateLcInit;
        end
      end

      FastPwrStateLcInit: begin
        lc_init = 1'b1;

        if (lc_done_i) begin
          state_d = FastPwrStateFlashInit;

        end
      end

      FastPwrStateFlashInit: begin
        flash_init_d = 1'b1;

        if (flash_done_i) begin
          state_d = FastPwrStateAckPwrUp;
        end
      end


      FastPwrStateAckPwrUp: begin
        // only ack the slow_fsm if we actually transitioned through it
        ack_pwrup_d = !reset_ongoing_q;

        // wait for request power up to drop relative to ack
        if (!req_pwrup_i || reset_ongoing_q) begin
          ack_pwrup_d = 1'b0;
          clr_cfg_lock_o = 1'b1;
          wkup_o = pwrup_cause_i == Wake;
          state_d = FastPwrStateActive;
        end
      end

      FastPwrStateActive: begin
        rst_sys_req_d = '0;
        reset_cause_d = ResetNone;

        if (reset_req || low_power_entry_i) begin
          reset_cause_d = ResetUndefined;
          state_d = FastPwrStateDisClks;
        end
      end

      FastPwrStateDisClks: begin
        ip_clk_en_d = 1'b0;

        if (!clk_en_status_i) begin
          state_d = reset_req ? FastPwrStateNvmShutDown : FastPwrStateFallThrough;
          wkup_record_o = ~reset_req;
        end
      end

      // Low Power Path
      FastPwrStateFallThrough: begin
        clr_hint_o = 1'b1;

        // the processor was interrupted after it asserted WFI and is executing again
        if (!low_power_entry_i) begin
          ip_clk_en_d = 1'b1;
          wkup_o = 1'b1;
          fall_through_o = 1'b1;
          state_d = FastPwrStateActive;
        end else begin
          state_d = FastPwrStateNvmIdleChk;
        end
      end

      FastPwrStateNvmIdleChk: begin

        if (otp_idle_i && lc_idle_i && flash_idle_i) begin
          state_d = FastPwrStateLowPowerPrep;
        end else begin
          ip_clk_en_d = 1'b1;
          wkup_o = 1'b1;
          abort_o = 1'b1;
          state_d = FastPwrStateActive;
        end
      end

      FastPwrStateLowPowerPrep: begin
        reset_cause_d = LowPwrEntry;

        // reset non-always-on domains if requested
        // this includes the clock manager, which implies pwr/rst managers must
        // be fed directly from the source
        for (int i = OffDomainSelStart; i < PowerDomains; i++) begin
          rst_lc_req_d[i] = ~main_pd_ni;
          rst_sys_req_d[i] = ~main_pd_ni;
        end

        if (reset_valid) begin
          state_d = FastPwrStateReqPwrDn;
        end
      end

      FastPwrStateReqPwrDn: begin
        req_pwrdn_d = 1'b1;

        if (ack_pwrdn_i) begin
          req_pwrdn_d = 1'b0;
          state_d = FastPwrStateLowPower;
        end
      end

      // Reset Path
      // This state is TODO, the details are still under discussion
      FastPwrStateNvmShutDown: begin
        clr_hint_o = 1'b1;
        reset_ongoing_d = 1'b1;
        state_d = FastPwrStateResetPrep;
      end

      FastPwrStateResetPrep: begin
        reset_cause_d = HwReq;
        rst_lc_req_d = {PowerDomains{1'b1}};
        rst_sys_req_d = {PowerDomains{1'b1}};

        if (reset_valid) begin
          state_d = FastPwrStateLowPower;
        end
      end

      // Terminal state, kill everything
      default: begin
        rst_lc_req_d = {PowerDomains{1'b1}};
        rst_sys_req_d = {PowerDomains{1'b1}};
        ip_clk_en_d = 1'b0;
      end

    endcase // unique case (state_q)
  end // always_comb

  assign ack_pwrup_o = ack_pwrup_q;
  assign req_pwrdn_o = req_pwrdn_q;

  assign pwr_rst_o.rst_lc_req = rst_lc_req_q;
  assign pwr_rst_o.rst_sys_req = rst_sys_req_q;
  assign pwr_rst_o.reset_cause = reset_cause_q;
  assign pwr_rst_o.rstreqs = reset_reqs_i;

  assign ips_clk_en_o = ip_clk_en_q;

  prim_flop #(
    .Width(1),
    // TODO: Is a value of 1 correct here?
    .ResetValue(1'b1)
  ) u_reg_flash_init (
    .clk_i,
    .rst_ni,
    .d_i(flash_init_d),
    .q_o(flash_init_o)
  );

  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_reg_otp_init (
    .clk_i,
    .rst_ni,
    .d_i(otp_init),
    .q_o(otp_init_o)
  );

  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_reg_lc_init (
    .clk_i,
    .rst_ni,
    .d_i(lc_init),
    .q_o(lc_init_o)
  );


endmodule
