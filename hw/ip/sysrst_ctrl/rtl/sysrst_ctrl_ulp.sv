// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl ULP module

module sysrst_ctrl_ulp import sysrst_ctrl_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_aon_ni,
  input  clk_i,
  input  rst_ni,

  input  lid_open_int,
  input  ac_present_int,
  input  pwrb_int,

  input  sysrst_ctrl_reg2hw_ulp_ac_debounce_ctl_reg_t ulp_ac_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_ulp_lid_debounce_ctl_reg_t ulp_lid_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_ulp_pwrb_debounce_ctl_reg_t ulp_pwrb_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_ulp_ctl_reg_t ulp_ctl_i,

  output sysrst_ctrl_hw2reg_ulp_status_reg_t ulp_status_o,
  output ulp_wakeup_o,
  output z3_wakeup_hw

);

  logic         cfg_ulp_en;
  logic         load_ulp_ac_timer;
  logic [15:0]  cfg_ulp_ac_timer;
  logic [15:0]  cfg_ulp_ac_timer_d;
  logic         load_ulp_lid_timer;
  logic [15:0]  cfg_ulp_lid_timer;
  logic [15:0]  cfg_ulp_lid_timer_d;
  logic         load_ulp_pwrb_timer;
  logic [15:0]  cfg_ulp_pwrb_timer;
  logic [15:0]  cfg_ulp_pwrb_timer_d;

  logic pwrb_cond_met, pwrb_cond_met_q;
  logic lid_open_cond_met, lid_open_cond_met_q;
  logic ac_present_cond_met, ac_present_cond_met_q;
  logic pwrb_int_i;
  logic lid_open_int_i;
  logic ac_present_int_i;
  logic pwrb_det_pulse;
  logic lid_open_det_pulse;
  logic ac_present_det_pulse;
  logic cfg_pwrb_det_pulse;
  logic cfg_lid_open_det_pulse;
  logic cfg_ac_present_det_pulse;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ulp_en (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(ulp_ctl_i.q),
    .q_o(cfg_ulp_en)
  );

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_ulp_ac_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (ulp_ac_debounce_ctl_i.qe),
    .wready_o  (),
    .wdata_i   (ulp_ac_debounce_ctl_i.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_aon_ni),
    .rvalid_o  (load_ulp_ac_timer),
    .rready_i  (1'b1),
    .rdata_o   (cfg_ulp_ac_timer_d),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_ulp_lid_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (ulp_lid_debounce_ctl_i.qe),
    .wready_o  (),
    .wdata_i   (ulp_lid_debounce_ctl_i.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_aon_ni),
    .rvalid_o  (load_ulp_lid_timer),
    .rready_i  (1'b1),
    .rdata_o   (cfg_ulp_lid_timer_d),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_ulp_pwrb_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (ulp_pwrb_debounce_ctl_i.qe),
    .wready_o  (),
    .wdata_i   (ulp_pwrb_debounce_ctl_i.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_aon_ni),
    .rvalid_o  (load_ulp_pwrb_timer),
    .rready_i  (1'b1),
    .rdata_o   (cfg_ulp_pwrb_timer_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_cfg_ulp_ac_timer_reg
    if (!rst_aon_ni) begin
      cfg_ulp_ac_timer    <= '0;
    end else if (load_ulp_ac_timer) begin
      cfg_ulp_ac_timer    <= cfg_ulp_ac_timer_d;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_cfg_ulp_lid_timer_reg
    if (!rst_aon_ni) begin
      cfg_ulp_lid_timer    <= '0;
    end else if (load_ulp_lid_timer) begin
      cfg_ulp_lid_timer    <= cfg_ulp_lid_timer_d;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_cfg_ulp_pwrb_timer_reg
    if (!rst_aon_ni) begin
      cfg_ulp_pwrb_timer    <= '0;
    end else if (load_ulp_pwrb_timer) begin
      cfg_ulp_pwrb_timer    <= cfg_ulp_pwrb_timer_d;
    end
  end

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_pwrb_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(pwrb_int),
    .q_o(pwrb_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_lid_open_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(lid_open_int),
    .q_o(lid_open_int_i)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_ac_present_in_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(ac_present_int),
    .q_o(ac_present_int_i)
  );

  sysrst_ctrl_ulpfsm # (
    .EDGE_TYPE("HL"),
    .TIMERBIT(16)
  ) i_pwrb_ulpfsm (
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .trigger_i(pwrb_int_i),
    .cfg_timer_i(cfg_ulp_pwrb_timer),
    .cfg_en_i(cfg_ulp_en),
    .timer_cond_met_o(pwrb_cond_met)
  );

  sysrst_ctrl_ulpfsm # (
    .EDGE_TYPE("LH"),
    .TIMERBIT(16)
  ) i_lid_open_ulpfsm (
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .trigger_i(lid_open_int_i),
    .cfg_timer_i(cfg_ulp_lid_timer),
    .cfg_en_i(cfg_ulp_en),
    .timer_cond_met_o(lid_open_cond_met)
  );

  sysrst_ctrl_ulpfsm # (
    .EDGE_TYPE("H"),
    .TIMERBIT(16)
  ) i_ac_present_ulpfsm (
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .trigger_i(ac_present_int_i),
    .cfg_timer_i(cfg_ulp_ac_timer),
    .cfg_en_i(cfg_ulp_en),
    .timer_cond_met_o(ac_present_cond_met)
  );

  //delay the level signal to generate a pulse
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_ulp_cond_met
    if (!rst_aon_ni) begin
      pwrb_cond_met_q    <= 1'b0;
      lid_open_cond_met_q    <= 1'b0;
      ac_present_cond_met_q    <= 1'b0;
    end else begin
      pwrb_cond_met_q    <= pwrb_cond_met;
      lid_open_cond_met_q    <= lid_open_cond_met;
      ac_present_cond_met_q    <= ac_present_cond_met;
    end
  end

  assign pwrb_det_pulse = cfg_ulp_en &&
    (pwrb_cond_met_q == 1'b0) && (pwrb_cond_met == 1'b1);
  assign lid_open_det_pulse = cfg_ulp_en &&
    (lid_open_cond_met_q == 1'b0) && (lid_open_cond_met == 1'b1);
  assign ac_present_det_pulse = cfg_ulp_en &&
    (ac_present_cond_met_q == 1'b0) && (ac_present_cond_met == 1'b1);

  //Synchronize from 200KHz always-onclock to 24MHz cfg clock
  prim_pulse_sync i_pwrb_det_pulse (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (pwrb_det_pulse),
    .dst_pulse_o (cfg_pwrb_det_pulse)
  );

  prim_pulse_sync i_lid_open_det_pulse (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (lid_open_det_pulse),
    .dst_pulse_o (cfg_lid_open_det_pulse)
  );

  prim_pulse_sync i_ac_present_det_pulse (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (ac_present_det_pulse),
    .dst_pulse_o (cfg_ac_present_det_pulse)
  );

  assign ulp_status_o.de =
           cfg_pwrb_det_pulse || cfg_lid_open_det_pulse || cfg_ac_present_det_pulse;

  assign ulp_status_o.d = 1'b1;

  assign ulp_wakeup_o =
           cfg_pwrb_det_pulse || cfg_lid_open_det_pulse || cfg_ac_present_det_pulse;

  assign z3_wakeup_hw = pwrb_cond_met || lid_open_cond_met || ac_present_cond_met;

endmodule
