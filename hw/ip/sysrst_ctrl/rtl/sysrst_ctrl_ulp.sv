// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl ULP module

module sysrst_ctrl_ulp import sysrst_ctrl_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_aon_ni,

  input  lid_open_int_i,
  input  ac_present_int_i,
  input  pwrb_int_i,

  input  sysrst_ctrl_reg2hw_ulp_ac_debounce_ctl_reg_t ulp_ac_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_ulp_lid_debounce_ctl_reg_t ulp_lid_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_ulp_pwrb_debounce_ctl_reg_t ulp_pwrb_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_ulp_ctl_reg_t ulp_ctl_i,

  output sysrst_ctrl_hw2reg_ulp_status_reg_t ulp_status_o,
  output ulp_wakeup_pulse_o,
  output z3_wakeup_hw_o

);

  logic pwrb_int;
  logic lid_open_int;
  logic ac_present_int;

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) u_pwrb_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(pwrb_int_i),
    .q_o(pwrb_int)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_lid_open_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(lid_open_int_i),
    .q_o(lid_open_int)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_ac_present_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(ac_present_int_i),
    .q_o(ac_present_int)
  );

  sysrst_ctrl_ulpfsm # (
    .EDGE_TYPE("HL"),
    .TIMERBIT(16)
  ) u_pwrb_ulpfsm (
    .clk_aon_i,
    .rst_aon_ni,
    .trigger_i(pwrb_int),
    .cfg_timer_i(ulp_pwrb_debounce_ctl_i.q),
    .cfg_en_i(ulp_ctl_i.q),
    .timer_cond_met_o(pwrb_cond_met_d)
  );

  sysrst_ctrl_ulpfsm # (
    .EDGE_TYPE("LH"),
    .TIMERBIT(16)
  ) u_lid_open_ulpfsm (
    .clk_aon_i,
    .rst_aon_ni,
    .trigger_i(lid_open_int),
    .cfg_timer_i(ulp_lid_debounce_ctl_i.q),
    .cfg_en_i(ulp_ctl_i.q),
    .timer_cond_met_o(lid_open_cond_met_d)
  );

  sysrst_ctrl_ulpfsm # (
    .EDGE_TYPE("H"),
    .TIMERBIT(16)
  ) u_ac_present_ulpfsm (
    .clk_aon_i,
    .rst_aon_ni,
    .trigger_i(ac_present_int),
    .cfg_timer_i(ulp_ac_debounce_ctl_i.q),
    .cfg_en_i(ulp_ctl_i.q),
    .timer_cond_met_o(ac_present_cond_met_d)
  );

  //delay the level signal to generate a pulse
  logic pwrb_cond_met_d, pwrb_cond_met_q;
  logic lid_open_cond_met_d, lid_open_cond_met_q;
  logic ac_present_cond_met_d, ac_present_cond_met_q;
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: p_ulp_cond_met
    if (!rst_aon_ni) begin
      pwrb_cond_met_q       <= 1'b0;
      lid_open_cond_met_q   <= 1'b0;
      ac_present_cond_met_q <= 1'b0;
    end else begin
      pwrb_cond_met_q       <= pwrb_cond_met_d;
      lid_open_cond_met_q   <= lid_open_cond_met_d;
      ac_present_cond_met_q <= ac_present_cond_met_d;
    end
  end

  logic pwrb_det_pulse;
  logic lid_open_det_pulse;
  logic ac_present_det_pulse;
  assign pwrb_det_pulse       = pwrb_cond_met_d       & ~pwrb_cond_met_q;
  assign lid_open_det_pulse   = lid_open_cond_met_d   & ~lid_open_cond_met_q;
  assign ac_present_det_pulse = ac_present_cond_met_d & ~ac_present_cond_met_q;

  // aggregate pulses
  assign ulp_wakeup_pulse_o = ulp_ctl_i.q & (pwrb_det_pulse |
                                             lid_open_det_pulse |
                                             ac_present_det_pulse);

  assign z3_wakeup_hw_o = pwrb_cond_met_d |
                          lid_open_cond_met_d |
                          ac_present_cond_met_d;

  assign ulp_status_o.d = 1'b1;
  assign ulp_status_o.de = ulp_wakeup_pulse_o;

endmodule
