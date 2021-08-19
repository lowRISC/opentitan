// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl combo Module
//
module sysrst_ctrl_combo
  import sysrst_ctrl_reg_pkg::*;
(
  input                                                                clk_i,
  input                                                                rst_ni,
  // (Optionally) inverted input signals on AON clock
  input                                                                pwrb_int_i,
  input                                                                key0_int_i,
  input                                                                key1_int_i,
  input                                                                key2_int_i,
  input                                                                ac_present_int_i,
  input                                                                ec_rst_l_int_i,
  // CSRs synced to AON clock
  input  sysrst_ctrl_reg2hw_ec_rst_ctl_reg_t                           ec_rst_ctl_i,
  input  sysrst_ctrl_reg2hw_key_intr_debounce_ctl_reg_t                key_intr_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_com_sel_ctl_mreg_t          [NumCombo-1:0] com_sel_ctl_i,
  input  sysrst_ctrl_reg2hw_com_det_ctl_mreg_t          [NumCombo-1:0] com_det_ctl_i,
  input  sysrst_ctrl_reg2hw_com_out_ctl_mreg_t          [NumCombo-1:0] com_out_ctl_i,
  output sysrst_ctrl_hw2reg_combo_intr_status_reg_t                    combo_intr_status_o,
  // Output signals on AON clock
  output                                                               sysrst_ctrl_combo_intr_o,
  output                                                               bat_disable_hw_o,
  output                                                               rst_req_o,
  output                                                               ec_rst_l_hw_o
);

  // There are four possible combos
  // Each key combo can select different triggers
  logic [NumCombo-1:0] combo_bat_disable;
  logic [NumCombo-1:0] combo_ec_rst_l;
  logic [NumCombo-1:0] combo_rst_req;
  logic [NumCombo-1:0] combo_intr_pulse;

  logic [4:0] in;
  assign in = {pwrb_int_i, key0_int_i, key1_int_i, key2_int_i, ac_present_int_i};

  for (genvar k = 0; k < NumCombo; k++) begin : gen_combo_trigger
    // Generate the trigger for each combo
    logic [4:0] cfg_in_sel;
    assign cfg_in_sel = {
      com_sel_ctl_i[k].pwrb_in_sel.q,
      com_sel_ctl_i[k].key0_in_sel.q,
      com_sel_ctl_i[k].key1_in_sel.q,
      com_sel_ctl_i[k].key2_in_sel.q,
      com_sel_ctl_i[k].ac_present_sel.q
    };

    // If the config bits are all-zero, we tie both trigger outputs to zero.
    // Otherwise:
    //           - assert trigger_h_o when all selected bits are 1
    //           - assert trigger_l_o when all selected bits are 0
    logic trigger_h, trigger_l;
    assign trigger_h = (|cfg_in_sel) && ((in & cfg_in_sel) == cfg_in_sel);
    assign trigger_l = (|cfg_in_sel) && ((in & cfg_in_sel) == '0);

    logic cfg_combo_en;
    assign cfg_combo_en = com_sel_ctl_i[k].pwrb_in_sel.q |
                          com_sel_ctl_i[k].key0_in_sel.q |
                          com_sel_ctl_i[k].key1_in_sel.q |
                          com_sel_ctl_i[k].key2_in_sel.q |
                          com_sel_ctl_i[k].ac_present_sel.q;

    //Instantiate the combo detection state machine
    logic combo_det;
    sysrst_ctrl_combofsm #(
      .Timer1Width(TimerWidth),
      .Timer2Width(DetTimerWidth)
    ) u_combo_fsm (
      .clk_i,
      .rst_ni,
      .trigger_h_i(trigger_h),
      .trigger_l_i(trigger_l),
      .cfg_timer1_i(key_intr_debounce_ctl_i.q),
      .cfg_timer2_i(com_det_ctl_i[k].q),
      .cfg_h2l_en_i(cfg_combo_en),
      .timer_h2l_cond_met_o(combo_det)
    );

    //Instantiate the combo action module
    sysrst_ctrl_comboact u_combo_act (
      .clk_i,
      .rst_ni,
      .cfg_intr_en_i(com_out_ctl_i[k].interrupt.q),
      .cfg_bat_disable_en_i(com_out_ctl_i[k].bat_disable.q),
      .cfg_ec_rst_en_i(com_out_ctl_i[k].ec_rst.q),
      .cfg_rst_req_en_i(com_out_ctl_i[k].rst_req.q),
      .combo_det_i(combo_det),
      .ec_rst_l_i(ec_rst_l_int_i),
      .ec_rst_ctl_i(ec_rst_ctl_i),
      .combo_intr_pulse_o(combo_intr_pulse[k]),
      .bat_disable_o(combo_bat_disable[k]),
      .rst_req_o(combo_rst_req[k]),
      .ec_rst_l_o(combo_ec_rst_l[k])
    );
  end

  // bat_disable
  // If any combo triggers bat_disable, assert the signal
  assign bat_disable_hw_o = |(combo_bat_disable);

  // If any combo triggers OT or EC RST(active low), assert the signal
  assign rst_req_o = |(combo_rst_req);
  assign ec_rst_l_hw_o = &(combo_ec_rst_l);

  // Write interrupt status registers using the synced IRQ pulses.
  assign {combo_intr_status_o.combo3_h2l.de,
          combo_intr_status_o.combo2_h2l.de,
          combo_intr_status_o.combo1_h2l.de,
          combo_intr_status_o.combo0_h2l.de} = combo_intr_pulse;

  assign sysrst_ctrl_combo_intr_o = |combo_intr_pulse;

  assign combo_intr_status_o.combo0_h2l.d = 1'b1;
  assign combo_intr_status_o.combo1_h2l.d = 1'b1;
  assign combo_intr_status_o.combo2_h2l.d = 1'b1;
  assign combo_intr_status_o.combo3_h2l.d = 1'b1;

endmodule
