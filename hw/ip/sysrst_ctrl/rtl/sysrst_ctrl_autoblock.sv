// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl PWRB autoblock module

module sysrst_ctrl_autoblock import sysrst_ctrl_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_aon_ni,

  input  pwrb_int_i,
  input  key0_int_i,
  input  key1_int_i,
  input  key2_int_i,

  input  sysrst_ctrl_reg2hw_auto_block_debounce_ctl_reg_t auto_block_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_auto_block_out_ctl_reg_t      auto_block_out_ctl_i,

  output pwrb_out_hw_o,
  output key0_out_hw_o,
  output key1_out_hw_o,
  output key2_out_hw_o
);

  logic ab_cond_met;
  logic pwrb_int;

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) u_pwrb_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(pwrb_int_i),
    .q_o(pwrb_int)
  );

  sysrst_ctrl_timerfsm # (
    .TIMERBIT(16)
  ) u_ab_fsm (
    .clk_aon_i,
    .rst_aon_ni,
    .trigger_i(pwrb_int),
    .cfg_timer_i(auto_block_debounce_ctl_i.debounce_timer.q),
    .cfg_l2h_en_i(1'b0),
    .cfg_h2l_en_i(auto_block_debounce_ctl_i.auto_block_enable.q),
    .timer_l2h_cond_met(),
    .timer_h2l_cond_met(ab_cond_met)
  );

  assign pwrb_out_hw_o = pwrb_int;
  assign key0_out_hw_o = (ab_cond_met & auto_block_out_ctl_i.key0_out_sel.q) ?
                         auto_block_out_ctl_i.key0_out_value.q : key0_int_i;
  assign key1_out_hw_o = (ab_cond_met & auto_block_out_ctl_i.key1_out_sel.q) ?
                         auto_block_out_ctl_i.key1_out_value.q : key1_int_i;
  assign key2_out_hw_o = (ab_cond_met & auto_block_out_ctl_i.key2_out_sel.q) ?
                         auto_block_out_ctl_i.key2_out_value.q : key2_int_i;

endmodule
