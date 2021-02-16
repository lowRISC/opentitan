// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description RBOX PWRB autoblock module

module rbox_autoblock import rbox_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_slow_ni,
  input  clk_i,
  input  rst_ni,

  input  pwrb_int,
  input  key0_int,
  input  key1_int,
  input  key2_int,

  input  rbox_reg2hw_auto_block_debounce_ctl_reg_t auto_block_debounce_ctl_i,
  input  rbox_reg2hw_auto_block_out_ctl_reg_t      auto_block_out_ctl_i,

  output pwrb_out_hw,
  output key0_out_hw,
  output key1_out_hw,
  output key2_out_hw

);

  logic         cfg_auto_block_en;
  logic         load_auto_block_timer;
  logic [15:0]  cfg_auto_block_timer;
  logic [15:0]  cfg_auto_block_timer_d;
  logic         cfg_key0_o_sel;
  logic         cfg_key1_o_sel;
  logic         cfg_key2_o_sel;
  logic         cfg_key0_o_q;
  logic         cfg_key1_o_q;
  logic         cfg_key2_o_q;

  logic ab_cond_met;
  logic pwrb_int_i;

  //nc_ means no connect
  logic nc_auto_block_enable;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_auto_block_en (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_debounce_ctl_i.auto_block_enable.q),
    .q_o(cfg_auto_block_en)
  );

  assign nc_auto_block_enable = auto_block_debounce_ctl_i.auto_block_enable.qe;

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_auto_block_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (auto_block_debounce_ctl_i.debounce_timer.qe),
    .wready_o  (),
    .wdata_i   (auto_block_debounce_ctl_i.debounce_timer.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_auto_block_timer),
    .rready_i  (1'b1),
    .rdata_o   (cfg_auto_block_timer_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_auto_block_timer_reg
    if (!rst_slow_ni) begin
      cfg_auto_block_timer    <= '0;
    end else if (load_auto_block_timer) begin
      cfg_auto_block_timer    <= cfg_auto_block_timer_d;
    end
  end

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_o_sel (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_out_ctl_i.key0_out_sel.q),
    .q_o(cfg_key0_o_sel)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_o_sel (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_out_ctl_i.key1_out_sel.q),
    .q_o(cfg_key1_o_sel)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_o_sel (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_out_ctl_i.key2_out_sel.q),
    .q_o(cfg_key2_o_sel)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_o_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_out_ctl_i.key0_out_value.q),
    .q_o(cfg_key0_o_q)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_o_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_out_ctl_i.key1_out_value.q),
    .q_o(cfg_key1_o_q)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_o_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(auto_block_out_ctl_i.key2_out_value.q),
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
    .TIMERBIT(16)
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
