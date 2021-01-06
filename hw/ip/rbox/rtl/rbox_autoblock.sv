// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description RBOX PWRB autoblock module

module rbox_autoblock (
  input               clk_aon_i,
  input               rst_slow_ni,
  input               clk_i,
  input               rst_ni,

  input               pwrb_int,
  input               key0_int,
  input               key1_int,
  input               key2_int,

  output              pwrb_out_hw,
  output              key0_out_hw,
  output              key1_out_hw,
  output              key2_out_hw

);
  import rbox_reg_pkg::*;

  rbox_reg2hw_t reg2hw;

  logic         cfg_auto_block_en;
  logic [15:0]  cfg_auto_block_timer;
  logic         cfg_key0_o_sel;
  logic         cfg_key1_o_sel;
  logic         cfg_key2_o_sel;
  logic         cfg_key0_o_q;
  logic         cfg_key1_o_q;
  logic         cfg_key2_o_q;

  logic [15:0] ab_cnt_d, ab_cnt_q;
  logic ab_cnt_clr, ab_cnt_en;
  logic ab_cond_met;
  logic pwrb_int_i, pwrb_int_q;
  logic pwrb_int_h2l, pwrb_int_l2h, pwrb_int_l2l;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_auto_block_en (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_debounce_ctl.auto_block_enable.q),
    .q_o(cfg_auto_block_en)
  );

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_auto_block_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.auto_block_debounce_ctl.debounce_timer.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.auto_block_debounce_ctl.debounce_timer.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_auto_block_timer),
    .rdepth_o  ()
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_o_sel (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_out_ctl.key0_out_sel.q),
    .q_o(cfg_key0_o_sel)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_o_sel (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_out_ctl.key1_out_sel.q),
    .q_o(cfg_key1_o_sel)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_o_sel (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_out_ctl.key2_out_sel.q),
    .q_o(cfg_key2_o_sel)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_o_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_out_ctl.key0_out_value.q),
    .q_o(cfg_key0_o_q)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_o_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_out_ctl.key1_out_value.q),
    .q_o(cfg_key1_o_q)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_o_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.auto_block_out_ctl.key2_out_value.q),
    .q_o(cfg_key2_o_q)
  );

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_pwrb_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pwrb_int),
    .q_o(pwrb_int_i)
  );

  rbox_timerfsm # (
    .timerBit(16)
  ) i_ab_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(pwrb_int_i),
    .cfg_timer_i(cfg_auto_block_timer),
    .cfg_l2h_en_i(1'b0),
    .cfg_h2l_en_i(cfg_auto_block_en),
    .timer_l2h_cond_met(),
    .timer_h2l_cond_met(ab_cond_met)
  );

  assign pwrb_out_hw = pwrb_int;
  assign key0_out_hw = (ab_cond_met & cfg_key0_o_sel) ? cfg_key0_o_q : key0_int;
  assign key1_out_hw = (ab_cond_met & cfg_key1_o_sel) ? cfg_key1_o_q : key1_int;
  assign key2_out_hw = (ab_cond_met & cfg_key2_o_sel) ? cfg_key2_o_q : key2_int;

endmodule
