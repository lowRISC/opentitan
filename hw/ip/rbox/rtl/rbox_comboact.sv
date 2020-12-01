// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX combo action Module
//
module rbox_comboact (
  input               clk_aon_i,
  input               rst_slow_ni,
  input               clk_i,
  input               rst_ni,

  input   rbox_reg_pkg::rbox_reg2hw_t reg2hw,
  output  rbox_reg_pkg::rbox_hw2reg_t hw2reg,

  input               cfg_intr_en,
  input               cfg_bat_disable_en,
  input               cfg_ec_rst_en,
  input               cfg_gsc_rst_en,
  input               combo_det,
  input               ec_rst_l_i,

  output              combo_intr_pulse,
  output              bat_disable_o,
  output              gsc_rst_o,
  output              ec_rst_l_o
);

  import rbox_reg_pkg::*;

  logic [15:0]  cfg_ec_rst_timer;

  logic combo_det_q;
  logic combo_gsc_pulse;
  logic combo_bat_disable_pulse;
  logic bat_disable_q, bat_disable_d;
  logic gsc_rst_q, gsc_rst_d;
  logic combo_ec_rst_pulse;
  logic ec_rst_l_q, ec_rst_l_d;

  logic [15:0] timer_cnt_d, timer_cnt_q;
  logic timer_cnt_clr, timer_cnt_en;

  logic ec_rst_l_int, ec_rst_l_det;

  //delay the level signal to generate a pulse
  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_combo_det
    if (!rst_slow_ni) begin
      combo_det_q    <= 1'b0;
    end else begin
      combo_det_q    <= combo_det;
    end
  end

  //bat_disable logic
  assign combo_bat_disable_pulse = cfg_bat_disable_en && (combo_det_q == 1'b0) && (combo_det == 1'b1);

  assign bat_disable_d = combo_bat_disable_pulse ? 1'b1 : bat_disable_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_combo_bat_disable
    if (!rst_slow_ni) begin
      bat_disable_q    <= 1'b0;
    end else begin
      bat_disable_q    <= bat_disable_d;
    end
  end

  assign bat_disable_o = bat_disable_q;

  //Interrupt logic
  assign combo_intr_pulse = cfg_intr_en && (combo_det_q == 1'b0) && (combo_det == 1'b1);

  //ec_rst_logic
  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_fifo_async #(
    .Width(16),
    .Depth(1)
  ) i_cfg_ec_rst_pulse (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.ec_rst_ctl.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.ec_rst_ctl.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_ec_rst_timer),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_ec_rst_l_int
    if (!rst_slow_ni) begin
      ec_rst_l_int    <= 1'b1;//active low signal
    end else begin
      ec_rst_l_int    <= ec_rst_l_i;
    end
  end

  //ec_rst_l_i high->low detection
  assign ec_rst_l_det = (ec_rst_l_int == 1'b1) && (ec_rst_l_i == 1'b0);

  //combo with EC RST CFG enable
  assign combo_ec_rst_pulse = cfg_ec_rst_en && (combo_det_q == 1'b0) && (combo_det == 1'b1);

  //GSC reset will also reset EC
  assign ec_rst_l_d = (combo_ec_rst_pulse | combo_gsc_pulse | ec_rst_l_det) ? 1'b0 :
	  timer_cnt_clr ? 1'b1 : ec_rst_l_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_combo_ec_rst_l
    if (!rst_slow_ni) begin
      ec_rst_l_q    <= 1'b0;//asserted when power-on-reset is asserted
    end else begin
      ec_rst_l_q    <= ec_rst_l_d;
    end
  end

  assign timer_cnt_en = (ec_rst_l_q == 1'b0);

  assign timer_cnt_clr = (ec_rst_l_q == 1'b0) && (timer_cnt_q == cfg_ec_rst_timer);

  assign timer_cnt_d = (timer_cnt_en) ? timer_cnt_q + 1'b1 : timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: timer_cnt_regs
    if (!rst_slow_ni) begin
      timer_cnt_q    <= '0;
    end
      else if (timer_cnt_clr) begin
         timer_cnt_q <= '0;
      end else begin
         timer_cnt_q <= timer_cnt_d;
      end
    end
  end

  assign ec_rst_l_o = ec_rst_l_q;

  //gsc_rst_logic
  assign combo_gsc_pulse = cfg_gsc_rst_en && (combo_det_q == 1'b0) && (combo_det == 1'b1);

  assign gsc_rst_d = combo_gsc_pulse ? 1'b1 : gsc_rst_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_combo_gsc_rst
    if (!rst_slow_ni) begin
      gsc_rst_q    <= 1'b0;
    end else begin
      gsc_rst_q    <= gsc_rst_d;
    end
  end

  assign gsc_rst_o = gsc_rst_q;

endmodule
