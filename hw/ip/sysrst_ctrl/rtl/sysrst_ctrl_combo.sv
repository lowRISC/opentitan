// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl combo Module
//
module sysrst_ctrl_combo import sysrst_ctrl_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_aon_ni,
  input  clk_i,
  input  rst_ni,

  input  pwrb_int_i,
  input  key0_int_i,
  input  key1_int_i,
  input  key2_int_i,
  input  ac_present_int_i,
  input  cio_ec_rst_in_l_i,

  input  sysrst_ctrl_reg2hw_ec_rst_ctl_reg_t ec_rst_ctl_i,
  input  sysrst_ctrl_reg2hw_key_intr_debounce_ctl_reg_t key_intr_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_com_sel_ctl_mreg_t [NumCombo-1:0] com_sel_ctl_i,
  input  sysrst_ctrl_reg2hw_com_det_ctl_mreg_t [NumCombo-1:0] com_det_ctl_i,
  input  sysrst_ctrl_reg2hw_com_out_ctl_mreg_t [NumCombo-1:0] com_out_ctl_i,

  output sysrst_ctrl_hw2reg_combo_intr_status_reg_t combo_intr_status_o,
  output sysrst_ctrl_combo_intr_o,

  output bat_disable_hw_o,
  output gsc_rst_o,
  output ec_rst_l_hw_o
);

  // There are four possible combos
  // Each key combo can select different triggers
  logic pwrb_int;
  logic key0_int, key1_int, key2_int;
  logic ac_present_int;

  logic [NumCombo-1:0] trigger_h;
  logic [NumCombo-1:0] trigger_l;
  logic [NumCombo-1:0] cfg_combo_en;
  logic [NumCombo-1:0] combo_det;

  logic [NumCombo-1:0] combo_bat_disable;
  logic [NumCombo-1:0] combo_intr_pulse;
  logic [NumCombo-1:0] combo_intr_pulse_synced;
  logic [NumCombo-1:0] combo_ec_rst_l;
  logic [NumCombo-1:0] combo_gsc_rst;

  logic ec_rst_l_int;


  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) u_ec_rst_l_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(cio_ec_rst_in_l_i),
    .q_o(ec_rst_l_int)
  );

  //synchronize between GPIO and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) u_pwrb_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(pwrb_int_i),
    .q_o(pwrb_int)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_key0_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(key0_int_i),
    .q_o(key0_int)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_key1_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(key1_int_i),
    .q_o(key1_int)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_key2_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(key2_int_i),
    .q_o(key2_int)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_ac_present_int_i (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(ac_present_int_i),
    .q_o(ac_present_int)
  );

  for (genvar k = 0 ; k < NumCombo ; k++) begin : gen_combo_trigger
    // generate the trigger for each combo
    sysrst_ctrl_combotrg u_combo_trg (
      .cfg_in0_sel(com_sel_ctl_i[k].pwrb_in_sel.q),
      .cfg_in1_sel(com_sel_ctl_i[k].key0_in_sel.q),
      .cfg_in2_sel(com_sel_ctl_i[k].key1_in_sel.q),
      .cfg_in3_sel(com_sel_ctl_i[k].key2_in_sel.q),
      .cfg_in4_sel(com_sel_ctl_i[k].ac_present_sel.q),
      .in0(pwrb_int),
      .in1(key0_int),
      .in2(key1_int),
      .in3(key2_int),
      .in4(ac_present_int),
      .trigger_h_o(trigger_h[k]),
      .trigger_l_o(trigger_l[k])
    );

    assign cfg_combo_en[k] = com_sel_ctl_i[k].pwrb_in_sel.q |
                             com_sel_ctl_i[k].key0_in_sel.q |
                             com_sel_ctl_i[k].key1_in_sel.q |
                             com_sel_ctl_i[k].key2_in_sel.q |
                             com_sel_ctl_i[k].ac_present_sel.q;

    //Instantiate the combo detection state machine
    sysrst_ctrl_combofsm # (
      .TIMER1BIT(16),
      .TIMER2BIT(32)
    ) u_combo_fsm (
      .clk_aon_i,
      .rst_aon_ni,
      .trigger_h_i(trigger_h[k]),
      .trigger_l_i(trigger_l[k]),
      .cfg_timer1_i(key_intr_debounce_ctl_i.q),
      .cfg_timer2_i(com_det_ctl_i[k].q),
      .cfg_h2l_en_i(cfg_combo_en[k]),
      .timer_h2l_cond_met(combo_det[k])
    );

    //Instantiate the combo action module
    sysrst_ctrl_comboact u_combo_act (
      .clk_aon_i,
      .rst_aon_ni,
      .cfg_intr_en(com_out_ctl_i[k].interrupt.q),
      .cfg_bat_disable_en(com_out_ctl_i[k].bat_disable.q),
      .cfg_ec_rst_en(com_out_ctl_i[k].ec_rst.q),
      .cfg_gsc_rst_en(com_out_ctl_i[k].gsc_rst.q),
      .combo_det(combo_det[k]),
      .ec_rst_l_i(ec_rst_l_int),
      .ec_rst_ctl_i(ec_rst_ctl_i),
      .combo_intr_pulse(combo_intr_pulse[k]),
      .bat_disable_o(combo_bat_disable[k]),
      .gsc_rst_o(combo_gsc_rst[k]),
      .ec_rst_l_o(combo_ec_rst_l[k])
   );

    // Synchronize IRQ pulsefrom 200KHz always-onclock to 24MHz cfg clock
    prim_pulse_sync u_combo0_intr (
      .clk_src_i   (clk_aon_i),
      .clk_dst_i   (clk_i),
      .rst_src_ni  (rst_aon_ni),
      .rst_dst_ni  (rst_ni),
      .src_pulse_i (combo_intr_pulse[k]),
      .dst_pulse_o (combo_intr_pulse_synced[k])
    );
  end

  // bat_disable
  // If any combo triggers bat_disable, assert the signal
  assign bat_disable_hw_o = |(combo_bat_disable);

  // If any combo triggers GSC or EC RST(active low), assert the signal
  assign gsc_rst_o = |(combo_gsc_rst);
  assign ec_rst_l_hw_o = &(combo_ec_rst_l);

  // Write interrupt status registers using the synced IRQ pulses.
  assign {combo_intr_status_o.combo3_h2l.de,
          combo_intr_status_o.combo2_h2l.de,
          combo_intr_status_o.combo1_h2l.de,
          combo_intr_status_o.combo0_h2l.de} = combo_intr_pulse_synced;

  assign sysrst_ctrl_combo_intr_o = |combo_intr_pulse_synced;

  assign combo_intr_status_o.combo0_h2l.d = 1'b1;
  assign combo_intr_status_o.combo1_h2l.d = 1'b1;
  assign combo_intr_status_o.combo2_h2l.d = 1'b1;
  assign combo_intr_status_o.combo3_h2l.d = 1'b1;

endmodule
