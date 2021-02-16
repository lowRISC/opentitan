// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX combo Module
//
module rbox_combo import rbox_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_slow_ni,
  input  clk_i,
  input  rst_ni,

  input  pwrb_int,
  input  key0_int,
  input  key1_int,
  input  key2_int,
  input  ac_present_int,
  input  cio_ec_rst_l_i,

  input  rbox_reg2hw_ec_rst_ctl_reg_t ec_rst_ctl_i,
  input  rbox_reg2hw_key_intr_debounce_ctl_reg_t key_intr_debounce_ctl_i,
  input  rbox_reg2hw_com_sel_ctl_mreg_t [NumCombo-1:0] com_sel_ctl_i,
  input  rbox_reg2hw_com_det_ctl_mreg_t [NumCombo-1:0] com_det_ctl_i,
  input  rbox_reg2hw_com_out_ctl_mreg_t [NumCombo-1:0] com_out_ctl_i,

  output rbox_hw2reg_combo_intr_status_reg_t combo_intr_status_o,
  output rbox_combo_intr,

  output bat_disable_hw,
  output gsc_rst_o,
  output ec_rst_l_hw
);

  //There are four possible combos
  //Each key combo can select different triggers
  logic [NumCombo-1:0] cfg_key0_in_sel_com;
  logic [NumCombo-1:0] cfg_key1_in_sel_com;
  logic [NumCombo-1:0] cfg_key2_in_sel_com;
  logic [NumCombo-1:0] cfg_pwrb_in_sel_com;
  logic [NumCombo-1:0] cfg_ac_present_sel_com;

  logic [31:0] cfg_combo_timer [NumCombo];
  logic [15:0] cfg_debounce_timer;

  logic [NumCombo-1:0] load_combo_timer;
  logic load_debounce_timer;

  logic [31:0] cfg_combo_timer_d [NumCombo];
  logic [15:0] cfg_debounce_timer_d;

  logic [NumCombo-1:0] cfg_bat_disable_com;
  logic [NumCombo-1:0] cfg_intr_com;
  logic [NumCombo-1:0] cfg_ec_rst_com;
  logic [NumCombo-1:0] cfg_gsc_rst_com;

  logic pwrb_int_i;
  logic key0_int_i, key1_int_i, key2_int_i;
  logic ac_present_int_i;

  logic [NumCombo-1:0] trigger_h;
  logic [NumCombo-1:0] trigger_l;
  logic [NumCombo-1:0] cfg_combo_en;
  logic [NumCombo-1:0] combo_det;

  logic [NumCombo-1:0] combo_bat_disable;
  logic [NumCombo-1:0] combo_intr_pulse;
  logic [NumCombo-1:0] combo_ec_rst_l;
  logic [NumCombo-1:0] combo_gsc_rst;

  logic ec_rst_l_int_i;

  logic combo0_h2l_intr, combo1_h2l_intr, combo2_h2l_intr, combo3_h2l_intr;

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_ec_rst_l_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(cio_ec_rst_l_i),
    .q_o(ec_rst_l_int_i)
  );

  //synchronize between cfg(24MHz) and always-on(200KHz)
  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_com_sel
    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_sel_key0 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_sel_ctl_i[k].key0_in_sel.q),
    .q_o(cfg_key0_in_sel_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_sel_key1 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_sel_ctl_i[k].key1_in_sel.q),
    .q_o(cfg_key1_in_sel_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_sel_key2 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_sel_ctl_i[k].key2_in_sel.q),
    .q_o(cfg_key2_in_sel_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_sel_pwrb (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_sel_ctl_i[k].pwrb_in_sel.q),
    .q_o(cfg_pwrb_in_sel_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_sel_ac_present (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_sel_ctl_i[k].ac_present_sel.q),
    .q_o(cfg_ac_present_sel_com[k])
  );
  end

  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_com_det
    prim_fifo_async #(
    .Width(32),
    .Depth(2)
  ) i_cfg_combo_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (com_det_ctl_i[k].qe),
    .wready_o  (),
    .wdata_i   (com_det_ctl_i[k].q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_combo_timer[k]),
    .rready_i  (1'b1),
    .rdata_o   (cfg_combo_timer_d[k]),
    .rdepth_o  ()
  );

    always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_combo_timer_reg
      if (!rst_slow_ni) begin
        cfg_combo_timer[k]    <= '0;
      end else if (load_combo_timer[k]) begin
        cfg_combo_timer[k]    <= cfg_combo_timer_d[k];
      end
    end
  end

  prim_fifo_async #(
    .Width(16),
    .Depth(2)
  ) i_cfg_debounce_timer (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (key_intr_debounce_ctl_i.qe),
    .wready_o  (),
    .wdata_i   (key_intr_debounce_ctl_i.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_debounce_timer),
    .rready_i  (1'b1),
    .rdata_o   (cfg_debounce_timer_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_debounce_timer_reg
    if (!rst_slow_ni) begin
      cfg_debounce_timer    <= '0;
    end else if (load_debounce_timer) begin
      cfg_debounce_timer    <= cfg_debounce_timer_d;
    end
  end

  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_com_out
    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_bat_disable (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_out_ctl_i[k].bat_disable.q),
    .q_o(cfg_bat_disable_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_intr (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_out_ctl_i[k].interrupt.q),
    .q_o(cfg_intr_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_ec_rst (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_out_ctl_i[k].ec_rst.q),
    .q_o(cfg_ec_rst_com[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_com_gsc_rst (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(com_out_ctl_i[k].gsc_rst.q),
    .q_o(cfg_gsc_rst_com[k])
  );
  end

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

  //generate the trigger for each combo
  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_combo_trigger
    rbox_combotrg i_combo_trg (
      .cfg_in0_sel(cfg_pwrb_in_sel_com[k]),
      .cfg_in1_sel(cfg_key0_in_sel_com[k]),
      .cfg_in2_sel(cfg_key1_in_sel_com[k]),
      .cfg_in3_sel(cfg_key2_in_sel_com[k]),
      .cfg_in4_sel(cfg_ac_present_sel_com[k]),
      .in0(pwrb_int_i),
      .in1(key0_int_i),
      .in2(key1_int_i),
      .in3(key2_int_i),
      .in4(ac_present_int_i),
      .trigger_h_o(trigger_h[k]),
      .trigger_l_o(trigger_l[k])
    );
    assign cfg_combo_en[k] = cfg_pwrb_in_sel_com[k] | cfg_key0_in_sel_com[k] |
      cfg_key1_in_sel_com[k] | cfg_key2_in_sel_com[k] |
      cfg_ac_present_sel_com[k];
  end

  //Instantiate the combo detection state machine
  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_combofsm
    rbox_combofsm # (
      .TIMER1BIT(16),
      .TIMER2BIT(32)
    ) i_combo_fsm (
      .clk_aon_i(clk_aon_i),
      .rst_slow_ni(rst_slow_ni),
      .trigger_h_i(trigger_h[k]),
      .trigger_l_i(trigger_l[k]),
      .cfg_timer1_i(cfg_debounce_timer),
      .cfg_timer2_i(cfg_combo_timer[k]),
      .cfg_h2l_en_i(cfg_combo_en[k]),
      .timer_h2l_cond_met(combo_det[k])
    );
  end

  //Instantiate the combo action module
  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_combo_act
    rbox_comboact i_combo_act (
      .clk_aon_i(clk_aon_i),
      .rst_slow_ni(rst_slow_ni),
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .cfg_intr_en(cfg_intr_com[k]),
      .cfg_bat_disable_en(cfg_bat_disable_com[k]),
      .cfg_ec_rst_en(cfg_ec_rst_com[k]),
      .cfg_gsc_rst_en(cfg_gsc_rst_com[k]),
      .combo_det(combo_det[k]),
      .ec_rst_l_i(ec_rst_l_int_i),
      .ec_rst_ctl_i(ec_rst_ctl_i),
      .combo_intr_pulse(combo_intr_pulse[k]),
      .bat_disable_o(combo_bat_disable[k]),
      .gsc_rst_o(combo_gsc_rst[k]),
      .ec_rst_l_o(combo_ec_rst_l[k])
   );
  end

  //bat_disable
  //If any combo triggers bat_disable, assert the signal
  assign bat_disable_hw = |(combo_bat_disable);

  //If any combo triggers GSC or EC RST(active low), assert the signal
  assign gsc_rst_o = |(combo_gsc_rst);
  assign ec_rst_l_hw = &(combo_ec_rst_l);

  //Synchronize from 200KHz always-onclock to 24MHz cfg clock
  prim_pulse_sync i_combo0_intr (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (combo_intr_pulse[0]),
    .dst_pulse_o (combo0_h2l_intr)
  );

  assign combo_intr_status_o.combo0_h2l.de = combo0_h2l_intr;

  prim_pulse_sync i_combo1_intr (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (combo_intr_pulse[1]),
    .dst_pulse_o (combo1_h2l_intr)
  );

  assign combo_intr_status_o.combo1_h2l.de = combo1_h2l_intr;

  prim_pulse_sync i_combo2_intr (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (combo_intr_pulse[2]),
    .dst_pulse_o (combo2_h2l_intr)
  );

  assign combo_intr_status_o.combo2_h2l.de = combo2_h2l_intr;

  prim_pulse_sync i_combo3_intr (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (combo_intr_pulse[3]),
    .dst_pulse_o (combo3_h2l_intr)
  );

  assign combo_intr_status_o.combo3_h2l.de = combo3_h2l_intr;

  assign rbox_combo_intr = combo0_h2l_intr | combo1_h2l_intr | combo2_h2l_intr | combo3_h2l_intr;

  //To write into interrupt status register
  assign combo_intr_status_o.combo0_h2l.d = 1'b1;
  assign combo_intr_status_o.combo1_h2l.d = 1'b1;
  assign combo_intr_status_o.combo2_h2l.d = 1'b1;
  assign combo_intr_status_o.combo3_h2l.d = 1'b1;

endmodule
