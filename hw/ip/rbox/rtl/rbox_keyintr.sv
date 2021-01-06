// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX key-triggered interrupt Module
//
module rbox_keyintr (
  input               clk_aon_i,
  input               rst_slow_ni,
  input               clk_i,
  input               rst_ni,

  input               pwrb_int,
  input               key0_int,
  input               key1_int,
  input               key2_int,
  input               ac_present_int,
  input               cio_ec_rst_l_i

);

  import rbox_reg_pkg::*;

  rbox_reg2hw_t reg2hw;
  rbox_hw2reg_t hw2reg;

  logic         cfg_pwrb_in_h2l;
  logic         cfg_key0_in_h2l;
  logic         cfg_key1_in_h2l;
  logic         cfg_key2_in_h2l;
  logic         cfg_ac_present_h2l;
  logic         cfg_ec_rst_l_h2l;
  logic         cfg_pwrb_in_l2h;
  logic         cfg_key0_in_l2h;
  logic         cfg_key1_in_l2h;
  logic         cfg_key2_in_l2h;
  logic         cfg_ac_present_l2h;
  logic         cfg_ec_rst_l_l2h;

  logic [15:0]  cfg_key_intr_timer;

  logic pwrb_int_i;
  logic key0_int_i, key1_int_i, key2_int_i;
  logic ac_present_int_i;
  logic ec_rst_l_int_i;
  logic pwrb_intr_h2l_det, pwrb_intr_h2l_det_q, pwrb_intr_h2l_pulse;
  logic pwrb_intr_l2h_det, pwrb_intr_l2h_det_q, pwrb_intr_l2h_pulse;
  logic key0_intr_h2l_det, key0_intr_h2l_det_q, key0_intr_h2l_pulse;
  logic key0_intr_l2h_det, key0_intr_l2h_det_q, key0_intr_l2h_pulse;
  logic key1_intr_h2l_det, key1_intr_h2l_det_q, key1_intr_h2l_pulse;
  logic key1_intr_l2h_det, key1_intr_l2h_det_q, key1_intr_l2h_pulse;
  logic key2_intr_h2l_det, key2_intr_h2l_det_q, key2_intr_h2l_pulse;
  logic key2_intr_l2h_det, key2_intr_l2h_det_q, key2_intr_l2h_pulse;
  logic ac_present_intr_h2l_det, ac_present_intr_h2l_det_q, ac_present_intr_h2l_pulse;
  logic ac_present_intr_l2h_det, ac_present_intr_l2h_det_q, ac_present_intr_l2h_pulse;
  logic ec_rst_l_intr_h2l_det, ec_rst_l_intr_h2l_det_q, ec_rst_l_intr_h2l_pulse;
  logic ec_rst_l_intr_l2h_det, ec_rst_l_intr_l2h_det_q, ec_rst_l_intr_l2h_pulse;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_pwrb_in_h2l (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.pwrb_in_h2l.q),
    .q_o(cfg_pwrb_in_h2l)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_in_h2l (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.key0_in_h2l.q),
    .q_o(cfg_key0_in_h2l)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_in_h2l (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.key1_in_h2l.q),
    .q_o(cfg_key1_in_h2l)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_in_h2l (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.key2_in_h2l.q),
    .q_o(cfg_key2_in_h2l)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ac_present_h2l (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.ac_present_h2l.q),
    .q_o(cfg_ac_present_h2l)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ec_rst_l_h2l (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.ec_rst_l_h2l.q),
    .q_o(cfg_ec_rst_l_h2l)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_pwrb_in_l2h (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.pwrb_in_l2h.q),
    .q_o(cfg_pwrb_in_l2h)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_in_l2h (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.key0_in_l2h.q),
    .q_o(cfg_key0_in_l2h)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_in_l2h (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.key1_in_l2h.q),
    .q_o(cfg_key1_in_l2h)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_in_l2h (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.key2_in_l2h.q),
    .q_o(cfg_key2_in_l2h)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ac_present_l2h (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.ac_present_l2h.q),
    .q_o(cfg_ac_present_l2h)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ec_rst_l_l2h (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(reg2hw.key_intr_ctl.ec_rst_l_l2h.q),
    .q_o(cfg_ec_rst_l_l2h)
  );

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_key_intr_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.key_intr_debounce_ctl.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.key_intr_debounce_ctl.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_key_intr_timer),
    .rdepth_o  ()
  );

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_pwrb_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pwrb_int),
    .q_o(pwrb_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_key0_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key0_int),
    .q_o(key0_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_key1_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key1_int),
    .q_o(key1_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_key2_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key2_int),
    .q_o(key2_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_ac_present_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(ac_present_int),
    .q_o(ac_present_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_ec_rst_l_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(cio_ec_rst_l_i),
    .q_o(ec_rst_l_int_i)
  );

  //Instantiate the key state machine
  rbox_keyfsm # (
    .timerBit(16)
  ) i_pwrbintr_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(pwrb_int_i),
    .cfg_timer_i(cfg_key_intr_timer),
    .cfg_l2h_en_i(cfg_pwrb_in_l2h),
    .cfg_h2l_en_i(cfg_pwrb_in_h2l),
    .timer_l2h_cond_met(pwrb_intr_l2h_det),
    .timer_h2l_cond_met(pwrb_intr_h2l_det)
  );

  rbox_keyfsm # (
    .timerBit(16)
  ) i_key0intr_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(key0_int_i),
    .cfg_timer_i(cfg_key_intr_timer),
    .cfg_l2h_en_i(cfg_key0_in_l2h),
    .cfg_h2l_en_i(cfg_key0_in_h2l),
    .timer_l2h_cond_met(key0_intr_l2h_det),
    .timer_h2l_cond_met(key0_intr_h2l_det)
  );

  rbox_keyfsm # (
    .timerBit(16)
  ) i_key1intr_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(key1_int_i),
    .cfg_timer_i(cfg_key_intr_timer),
    .cfg_l2h_en_i(cfg_key1_in_l2h),
    .cfg_h2l_en_i(cfg_key1_in_h2l),
    .timer_l2h_cond_met(key1_intr_l2h_det),
    .timer_h2l_cond_met(key1_intr_h2l_det)
  );

  rbox_keyfsm # (
    .timerBit(16)
  ) i_key2intr_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(key2_int_i),
    .cfg_timer_i(cfg_key_intr_timer),
    .cfg_l2h_en_i(cfg_key2_in_l2h),
    .cfg_h2l_en_i(cfg_key2_in_h2l),
    .timer_l2h_cond_met(key2_intr_l2h_det),
    .timer_h2l_cond_met(key2_intr_h2l_det)
  );

  rbox_keyfsm # (
    .timerBit(16)
  ) i_ac_presentintr_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(ac_present_int_i),
    .cfg_timer_i(cfg_key_intr_timer),
    .cfg_l2h_en_i(cfg_ac_present_l2h),
    .cfg_h2l_en_i(cfg_ac_present_h2l),
    .timer_l2h_cond_met(ac_present_intr_l2h_det),
    .timer_h2l_cond_met(ac_present_intr_h2l_det)
  );

  rbox_keyfsm # (
    .timerBit(16)
  ) i_ec_rst_lintr_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .trigger_i(ec_rst_l_int_i),
    .cfg_timer_i(cfg_key_intr_timer),
    .cfg_l2h_en_i(cfg_ec_rst_l_l2h),
    .cfg_h2l_en_i(cfg_ec_rst_l_h2l),
    .timer_l2h_cond_met(ec_rst_l_intr_l2h_det),
    .timer_h2l_cond_met(ec_rst_l_intr_h2l_det)
  );


  //delay the level signal to generate a pulse
  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_pwrb_intr_h2l_det
    if (!rst_slow_ni) begin
      pwrb_intr_h2l_det_q    <= 1'b0;
    end else begin
      pwrb_intr_h2l_det_q    <= pwrb_intr_h2l_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_pwrb_intr_l2h_det
    if (!rst_slow_ni) begin
      pwrb_intr_l2h_det_q    <= 1'b0;
    end else begin
      pwrb_intr_l2h_det_q    <= pwrb_intr_l2h_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_key0_intr_h2l_det
    if (!rst_slow_ni) begin
      key0_intr_h2l_det_q    <= 1'b0;
    end else begin
      key0_intr_h2l_det_q    <= key0_intr_h2l_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_key0_intr_l2h_det
    if (!rst_slow_ni) begin
      key0_intr_l2h_det_q    <= 1'b0;
    end else begin
      key0_intr_l2h_det_q    <= key0_intr_l2h_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_key1_intr_h2l_det
    if (!rst_slow_ni) begin
      key1_intr_h2l_det_q    <= 1'b0;
    end else begin
      key1_intr_h2l_det_q    <= key1_intr_h2l_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_key1_intr_l2h_det
    if (!rst_slow_ni) begin
      key1_intr_l2h_det_q    <= 1'b0;
    end else begin
      key1_intr_l2h_det_q    <= key1_intr_l2h_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_key2_intr_h2l_det
    if (!rst_slow_ni) begin
      key2_intr_h2l_det_q    <= 1'b0;
    end else begin
      key2_intr_h2l_det_q    <= key2_intr_h2l_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_key2_intr_l2h_det
    if (!rst_slow_ni) begin
      key2_intr_l2h_det_q    <= 1'b0;
    end else begin
      key2_intr_l2h_det_q    <= key2_intr_l2h_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_ac_present_intr_h2l_det
    if (!rst_slow_ni) begin
      ac_present_intr_h2l_det_q    <= 1'b0;
    end else begin
      ac_present_intr_h2l_det_q    <= ac_present_intr_h2l_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_ac_present_intr_l2h_det
    if (!rst_slow_ni) begin
      ac_present_intr_l2h_det_q    <= 1'b0;
    end else begin
      ac_present_intr_l2h_det_q    <= ac_present_intr_l2h_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_ec_rst_l_intr_h2l_det
    if (!rst_slow_ni) begin
      ec_rst_l_intr_h2l_det_q    <= 1'b0;
    end else begin
      ec_rst_l_intr_h2l_det_q    <= ec_rst_l_intr_h2l_det;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_ec_rst_l_intr_l2h_det
    if (!rst_slow_ni) begin
      ec_rst_l_intr_l2h_det_q    <= 1'b0;
    end else begin
      ec_rst_l_intr_l2h_det_q    <= ec_rst_l_intr_l2h_det;
    end
  end

  //generate a pulse for interrupt status CSR
  assign pwrb_intr_l2h_pulse = (pwrb_intr_l2h_det_q == 1'b0) && (pwrb_intr_l2h_det == 1'b1);
  assign pwrb_intr_h2l_pulse = (pwrb_intr_h2l_det_q == 1'b1) && (pwrb_intr_h2l_det == 1'b0);
  assign key0_intr_l2h_pulse = (key0_intr_l2h_det_q == 1'b0) && (key0_intr_l2h_det == 1'b1);
  assign key0_intr_h2l_pulse = (key0_intr_h2l_det_q == 1'b1) && (key0_intr_h2l_det == 1'b0);
  assign key1_intr_l2h_pulse = (key1_intr_l2h_det_q == 1'b0) && (key1_intr_l2h_det == 1'b1);
  assign key1_intr_h2l_pulse = (key1_intr_h2l_det_q == 1'b1) && (key1_intr_h2l_det == 1'b0);
  assign key2_intr_l2h_pulse = (key2_intr_l2h_det_q == 1'b0) && (key2_intr_l2h_det == 1'b1);
  assign key2_intr_h2l_pulse = (key2_intr_h2l_det_q == 1'b1) && (key2_intr_h2l_det == 1'b0);
  assign ac_present_intr_l2h_pulse = (ac_present_intr_l2h_det_q == 1'b0) && (ac_present_intr_l2h_det == 1'b1);
  assign ac_present_intr_h2l_pulse = (ac_present_intr_h2l_det_q == 1'b1) && (ac_present_intr_h2l_det == 1'b0);
  assign ec_rst_l_intr_l2h_pulse = (ec_rst_l_intr_l2h_det_q == 1'b0) && (ec_rst_l_intr_l2h_det == 1'b1);
  assign ec_rst_l_intr_h2l_pulse = (ec_rst_l_intr_h2l_det_q == 1'b1) && (ec_rst_l_intr_h2l_det == 1'b0);

  //Synchronize from 200KHz always-onclock to 24MHz cfg clock
  prim_pulse_sync i_pwrb_h2l (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (pwrb_intr_h2l_pulse),
    .dst_pulse_o (hw2reg.intr_status.pwrb_h2l.de)
  );

  prim_pulse_sync i_pwrb_l2h (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (pwrb_intr_l2h_pulse),
    .dst_pulse_o (hw2reg.intr_status.pwrb_l2h.de)
  );

  prim_pulse_sync i_key0_in_h2l (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (key0_intr_h2l_pulse),
    .dst_pulse_o (hw2reg.intr_status.key0_in_h2l.de)
  );

  prim_pulse_sync i_key0_in_l2h (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (key0_intr_l2h_pulse),
    .dst_pulse_o (hw2reg.intr_status.key0_in_l2h.de)
  );

  prim_pulse_sync i_key1_in_h2l (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (key1_intr_h2l_pulse),
    .dst_pulse_o (hw2reg.intr_status.key1_in_h2l.de)
  );

  prim_pulse_sync i_key1_in_l2h (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (key1_intr_l2h_pulse),
    .dst_pulse_o (hw2reg.intr_status.key1_in_l2h.de)
  );

  prim_pulse_sync i_key2_in_h2l (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (key2_intr_h2l_pulse),
    .dst_pulse_o (hw2reg.intr_status.key2_in_h2l.de)
  );

  prim_pulse_sync i_key2_in_l2h (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (key2_intr_l2h_pulse),
    .dst_pulse_o (hw2reg.intr_status.key2_in_l2h.de)
  );

  prim_pulse_sync i_ac_present_h2l (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (ac_present_intr_h2l_pulse),
    .dst_pulse_o (hw2reg.intr_status.ac_present_h2l.de)
  );

  prim_pulse_sync i_ac_present_l2h (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (ac_present_intr_l2h_pulse),
    .dst_pulse_o (hw2reg.intr_status.ac_present_l2h.de)
  );

  prim_pulse_sync i_ec_rst_l_h2l (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (ec_rst_l_intr_h2l_pulse),
    .dst_pulse_o (hw2reg.intr_status.ec_rst_l_h2l.de)
  );

  prim_pulse_sync i_ec_rst_l_l2h (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (ec_rst_l_intr_l2h_pulse),
    .dst_pulse_o (hw2reg.intr_status.ec_rst_l_l2h.de)
  );

  //To write into interrupt status register
  assign hw2reg.intr_status.pwrb_h2l.d = 1'b1;
  assign hw2reg.intr_status.pwrb_l2h.d = 1'b1;
  assign hw2reg.intr_status.key0_in_h2l.d = 1'b1;
  assign hw2reg.intr_status.key0_in_l2h.d = 1'b1;
  assign hw2reg.intr_status.key1_in_h2l.d = 1'b1;
  assign hw2reg.intr_status.key1_in_l2h.d = 1'b1;
  assign hw2reg.intr_status.key2_in_h2l.d = 1'b1;
  assign hw2reg.intr_status.key2_in_l2h.d = 1'b1;
  assign hw2reg.intr_status.ac_present_h2l.d = 1'b1;
  assign hw2reg.intr_status.ac_present_l2h.d = 1'b1;
  assign hw2reg.intr_status.ec_rst_l_h2l.d = 1'b1;
  assign hw2reg.intr_status.ec_rst_l_l2h.d = 1'b1;

endmodule
