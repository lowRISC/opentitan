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
    input reset_req_i,

    // consumed in pwrmgr
    output logic capture_wkups_o,
    output logic dev_active_o,
    output logic fall_through_o,
    output logic abort_o,

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

  //// state enum
  //typedef enum logic [3:0] {
  //  StLowPower,
  //  StEnableClocks,
  //  StReleaseLcRst,
  //  StInitOtp,
  //  StInitLc,
  //  StAckPwrup,
  //  StActive,
  //  StDisClks,
  //  StNvmIdleChk,
  //  StLowPowerPrep,
  //  StNvmShutDown,
  //  StResetPrep,
  //  StReqPwrDn
  //} state_e;



  assign ack_pwrup_o = 1'b1;
  assign req_pwrdn_o = 1'b1;
  assign capture_wkups_o = 1'b0;
  assign dev_active_o = 1'b0;
  assign pwr_rst_o = '0;
  assign otp_init_o = 1'b0;
  assign lc_init_o = 1'b0;
  assign ips_clk_en_o = 1'b1;
  assign fall_through_o = 1'b0;
  assign abort_o = 1'b0;
  assign otp_status_req_o = 1'b0;
  assign lc_status_req_o = 1'b0;



endmodule
