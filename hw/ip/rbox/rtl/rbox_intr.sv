// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX interrupt Module
//
module rbox_intr (
  input   rbox_reg_pkg::rbox_reg2hw_t reg2hw,
  output  rbox_reg_pkg::rbox_hw2reg_t hw2reg,

  output              rbox_intr_o
);

  import rbox_reg_pkg::*;

  logic rbox_event;
  logic rbox_combo0_h2l_intr, rbox_combo1_h2l_intr, rbox_combo2_h2l_intr, rbox_combo3_h2l_intr;
  logic rbox_pwrb_h2l_intr, rbox_pwrb_l2h_intr;
  logic rbox_key0_h2l_intr, rbox_key0_l2h_intr;
  logic rbox_key1_h2l_intr, rbox_key1_l2h_intr;
  logic rbox_key2_h2l_intr, rbox_key2_l2h_intr;
  logic rbox_ac_present_h2l_intr, rbox_ac_present_l2h_intr;
  logic rbox_ec_rst_l_h2l_intr, rbox_ec_rst_l_l2h_intr;

  //reference the signals from CFG
  assign rbox_combo0_h2l_intr = hw2reg.intr_status.combo0_h2l.de;
  assign rbox_combo1_h2l_intr = hw2reg.intr_status.combo1_h2l.de;
  assign rbox_combo2_h2l_intr = hw2reg.intr_status.combo2_h2l.de;
  assign rbox_combo3_h2l_intr = hw2reg.intr_status.combo3_h2l.de;
  assign rbox_pwrb_h2l_intr = hw2reg.intr_status.pwrb_h2l.de;
  assign rbox_pwrb_l2h_intr = hw2reg.intr_status.pwrb_l2h.de;
  assign rbox_key0_h2l_intr = hw2reg.intr_status.key0_in_h2l.de;
  assign rbox_key0_l2h_intr = hw2reg.intr_status.key0_in_l2h.de;
  assign rbox_key1_h2l_intr = hw2reg.intr_status.key1_in_h2l.de;
  assign rbox_key1_l2h_intr = hw2reg.intr_status.key1_in_l2h.de;
  assign rbox_key2_h2l_intr = hw2reg.intr_status.key2_in_h2l.de;
  assign rbox_key2_l2h_intr = hw2reg.intr_status.key2_in_l2h.de;
  assign rbox_ac_present_h2l_intr = hw2reg.intr_status.ac_present_h2l.de;
  assign rbox_ac_present_l2h_intr = hw2reg.intr_status.ac_present_l2h.de;
  assign rbox_ec_rst_l_h2l_intr = hw2reg.intr_status.ec_rst_l_h2l.de;
  assign rbox_ec_rst_l_l2h_intr = hw2reg.intr_status.ec_rst_l_l2h.de;

  assign rbox_event = rbox_combo0_h2l_intr | rbox_combo1_h2l_intr | rbox_combo2_h2l_intr | rbox_combo3_h2l_intr |
	  rbox_pwrb_h2l_intr | rbox_pwrb_l2h_intr |
	  rbox_key0_h2l_intr | rbox_key0_l2h_intr |
	  rbox_key1_h2l_intr | rbox_key1_l2h_intr |
	  rbox_key2_h2l_intr | rbox_key2_l2h_intr |
	  rbox_ac_present_h2l_intr | rbox_ac_present_l2h_intr |
	  rbox_ec_rst_l_h2l_intr | rbox_ec_rst_l_l2h_intr;

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(1)) i_rbox_intr_o (
    .event_intr_i           (rbox_event),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.d),
    .intr_o                 (rbox_intr_o)
  );

endmodule
