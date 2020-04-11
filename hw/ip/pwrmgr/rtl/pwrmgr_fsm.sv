// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Fast FSM
//

`include "prim_assert.sv"

module pwrmgr_fsm import pwrmgr_pkg::*; (
  input clk_i,
  input rst_ni,

  // interface with slow_fsm
  input req_pwrup_i,
  input pwrup_cause_e pwrup_cause_i,
  output logic ack_pwrup_o,
  output logic req_pwrdn_o,
  input ack_pwrdn_i,
  input low_power_entry_i,
  input main_pdb_i,
  input reset_req_i,

  // consumed in pwrmgr
  output logic wkup_o,        // generate wake interrupt
  output logic wkup_record_o, // enable wakeup recording
  output logic fall_through_o,
  output logic abort_o,
  output logic clr_cfg_lock_o,

  // rstmgr
  output pwr_rst_req_t pwr_rst_o,
  input pwr_rst_rsp_t pwr_rst_i,

  // clkmgr
  output logic ips_clk_en_o,

  // otp
  output logic otp_init_o,
  input otp_done_i,
  input otp_idle_i,

  // lc
  output logic lc_init_o,
  input lc_done_i,
  input lc_idle_i,

  // flash
  input flash_idle_i
);

  // state enum
  typedef enum logic [3:0] {
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


  // all powered down domains have resets asserted
  logic pdb_rsts_asserted;

  // all domains have resets asserted
  logic all_rsts_asserted;

  // resets are valid
  logic reset_valid;

  // which powerdown path has been selected
  logic low_power_sel;

  // allow ndm_rst_req to take effect
  logic ndm_req_en;

  // reset causes fed to reset manager
  logic low_power_rst;
  logic hw_rst;

  state_e state_d, state_q;
  logic reset_ongoing_q, reset_ongoing_d;
  logic req_pwrdn_q, req_pwrdn_d;
  logic ack_pwrup_q, ack_pwrup_d;
  logic ip_clk_en_q, ip_clk_en_d;
  logic [PowerDomains-1:0] lc_rst_req_q, sys_rst_req_q;
  logic [PowerDomains-1:0] lc_rst_req_d, sys_rst_req_d;
  logic otp_init;
  logic lc_init;

  assign pdb_rsts_asserted = pwr_rst_i.rst_lc_src_n[PowerDomains-1:1] == '0 &
                             pwr_rst_i.rst_sys_src_n[PowerDomains-1:1] == '0;

  assign all_rsts_asserted = pwr_rst_i.rst_lc_src_n == '0 &&
                             pwr_rst_i.rst_sys_src_n == '0;

  // when in low power path, resets are controlled by domain power down
  // when in reset path, all resets must be asserted
  assign reset_valid = low_power_sel ? main_pdb_i | pdb_rsts_asserted :
                                       all_rsts_asserted;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StLowPower;
      ack_pwrup_q <= 1'b0;
      req_pwrdn_q <= 1'b0;
      reset_ongoing_q <= 1'b0;
      ip_clk_en_q <= 1'b0;
      lc_rst_req_q <= {PowerDomains-1{1'b1}};
      sys_rst_req_q <= {PowerDomains-1{1'b1}};
    end else begin
      state_q <= state_d;
      ack_pwrup_q <= ack_pwrup_d;
      req_pwrdn_q <= req_pwrdn_d;
      reset_ongoing_q <= reset_ongoing_d;
      ip_clk_en_q <= ip_clk_en_d;
      lc_rst_req_q <= lc_rst_req_d;
      sys_rst_req_q <= sys_rst_req_d;
    end
  end

  always_comb begin
    ack_pwrup_d = 1'b0;
    req_pwrdn_d = 1'b0;
    otp_init = 1'b0;
    lc_init = 1'b0;
    low_power_sel = 1'b1;
    wkup_o = 1'b0;
    wkup_record_o = 1'b0;
    fall_through_o = 1'b0;
    abort_o = 1'b0;
    ndm_req_en = 1'b0;
    clr_cfg_lock_o = 1'b0;
    low_power_rst = 1'b0;
    hw_rst = 1'b0;

    state_d = state_q;
    reset_ongoing_d = reset_ongoing_q;
    ip_clk_en_d = ip_clk_en_q;
    lc_rst_req_d = lc_rst_req_q;
    sys_rst_req_d = sys_rst_req_q;

    unique case(state_q)

      StLowPower: begin
        if (req_pwrup_i || reset_ongoing_q) begin
          state_d = StEnableClocks;
        end
      end

      StEnableClocks: begin
        ip_clk_en_d = 1'b1;

        if (1'b1) begin // TODO, add a feedback signal to check clocks are enabled
          state_d = StReleaseLcRst;
        end
      end

      StReleaseLcRst: begin
        lc_rst_req_d = '0;  // release rst_lc_n for all power domains

        if (&pwr_rst_i.rst_lc_src_n) begin // once all resets are released
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

        if (!req_pwrup_i || reset_ongoing_q) begin
          ack_pwrup_d = 1'b0;
          clr_cfg_lock_o = 1'b1;
          wkup_o = pwrup_cause_i == Wake;
          state_d = StActive;
        end
      end

      StActive: begin
        sys_rst_req_d = '0;
        ndm_req_en = 1'b1;

        if (reset_req_i || low_power_entry_i) begin
          state_d = StDisClks;
        end
      end

      StDisClks: begin
        ip_clk_en_d = 1'b0;

        if (1'b1) begin // TODO, add something to check that clocks are disabled
          state_d = reset_req_i ? StNvmShutDown : StFallThrough;
          wkup_record_o = !reset_req_i;
        end
      end

      // Low Power Path
      StFallThrough: begin

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
        // reset non-always-on domains if requested
        // this includes the clock manager, which implies pwr/rst managers must
        // be fed directly from the source
        for (int i = 1; i < PowerDomains; i++) begin
          lc_rst_req_d[i] = ~main_pdb_i;
          sys_rst_req_d[i] = ~main_pdb_i;
        end

        if (reset_valid) begin
          low_power_rst = 1'b1;
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
        reset_ongoing_d = 1'b1;
        state_d = StResetPrep;
      end

      StResetPrep: begin
        low_power_sel = 1'b0;
        lc_rst_req_d = {PowerDomains-1{1'b1}};
        sys_rst_req_d = {PowerDomains-1{1'b1}};

        if (reset_valid) begin
          hw_rst = 1'b1;
          state_d = StLowPower;
        end
      end

      // Terminal state, kill everything
      default: begin
        lc_rst_req_d = {PowerDomains-1{1'b1}};
        sys_rst_req_d = {PowerDomains-1{1'b1}};
        ip_clk_en_d = 1'b0;
      end

    endcase // unique case (state_q)
  end // always_comb

  assign ack_pwrup_o = ack_pwrup_q;
  assign req_pwrdn_o = req_pwrdn_q;

  assign pwr_rst_o.lc_rst_req = lc_rst_req_q;
  assign pwr_rst_o.sys_rst_req = sys_rst_req_q;
  assign pwr_rst_o.low_power_rst = low_power_rst;
  assign pwr_rst_o.hw_rst = hw_rst;
  assign pwr_rst_o.ndm_req_en = ndm_req_en;

  assign otp_init_o = otp_init;
  assign lc_init_o = lc_init;
  assign ips_clk_en_o = ip_clk_en_q;

endmodule
