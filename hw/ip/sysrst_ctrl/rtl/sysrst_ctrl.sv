// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// sysrst_ctrl module

`include "prim_assert.sv"

module sysrst_ctrl (
  input clk_i,//Always-on 24MHz clock(config)
  input clk_aon_i,//Always-on 200KHz clock(logic)
  input rst_ni,//power-on reset for the 24MHz clock(config)
  input rst_aon_ni,//power-on reset for the 200KHz clock(logic)
  output gsc_wk_o, //GSC wake to pwrmgr
  output gsc_rst_o,//GSC reset to rstmgr
  output intr_sysrst_ctrl_o,//sysrst_ctrl interrupt to PLIC

  //Regster interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  //DIO
  input  cio_ac_present_i,//AC power is present
  input  cio_ec_rst_in_l_i,//EC reset is asserted by some other system agent
  input  cio_key0_in_i,//VolUp button in tablet; column output from the EC in a laptop
  input  cio_key1_in_i,//VolDown button in tablet; row input from keyboard matrix in a laptop
  input  cio_key2_in_i,//TBD button in tablet; row input from keyboard matrix in a laptop
  input  cio_pwrb_in_i,//Power button in both tablet and laptop
  output logic cio_bat_disable_o,//Battery is disconnected
  output logic cio_ec_rst_out_l_o,//EC reset is asserted by sysrst_ctrl
  output logic cio_key0_out_o,//Passthrough from key0_in, can be configured to invert
  output logic cio_key1_out_o,//Passthrough from key1_in, can be configured to invert
  output logic cio_key2_out_o,//Passthrough from key2_in, can be configured to invert
  output logic cio_pwrb_out_o,//Passthrough from pwrb_in, can be configured to invert
  output logic cio_bat_disable_en_o,
  output logic cio_ec_rst_out_l_en_o,
  output logic cio_key0_out_en_o,
  output logic cio_key1_out_en_o,
  output logic cio_key2_out_en_o,
  output logic cio_pwrb_out_en_o
);

  import sysrst_ctrl_reg_pkg::* ;

  sysrst_ctrl_reg2hw_t reg2hw;
  sysrst_ctrl_hw2reg_t hw2reg;

  logic pwrb_int, key0_int, key1_int, key2_int, ac_present_int;
  logic pwrb_out_hw, key0_out_hw, key1_out_hw, key2_out_hw, ec_rst_l_hw, bat_disable_hw;
  logic pwrb_out_int, key0_out_int, key1_out_int, key2_out_int, bat_disable_int;
  logic sysrst_ctrl_combo_intr, sysrst_ctrl_key_intr;
  logic unused_intg_err_o;//FIXME

  //Always-on pins
  assign cio_ec_rst_out_l_en_o = 1'b1;
  assign cio_pwrb_out_en_o = 1'b1;
  assign cio_key0_out_en_o = 1'b1;
  assign cio_key1_out_en_o = 1'b1;
  assign cio_key2_out_en_o = 1'b1;
  assign cio_bat_disable_en_o = 1'b1;

  // Register module
  sysrst_ctrl_reg_top u_reg (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .tl_i(tl_i),
    .tl_o(tl_o),
    .reg2hw(reg2hw),
    .hw2reg(hw2reg),
    .intg_err_o(unused_intg_err_o),
    .devmode_i  (1'b1)
  );

  //Instantiate the autoblock module
  sysrst_ctrl_autoblock u_autoblock (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .pwrb_int(pwrb_int),
    .key0_int(key0_int),
    .key1_int(key1_int),
    .key2_int(key2_int),
    .auto_block_debounce_ctl_i(reg2hw.auto_block_debounce_ctl),
    .auto_block_out_ctl_i(reg2hw.auto_block_out_ctl),
    .pwrb_out_hw(pwrb_out_hw),
    .key0_out_hw(key0_out_hw),
    .key1_out_hw(key1_out_hw),
    .key2_out_hw(key2_out_hw)
  );

  //Instantiate the pin inversion module
  sysrst_ctrl_inv u_inversion (
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .cio_pwrb_in_i(cio_pwrb_in_i),
    .cio_key0_in_i(cio_key0_in_i),
    .cio_key1_in_i(cio_key1_in_i),
    .cio_key2_in_i(cio_key2_in_i),
    .cio_ac_present_i(cio_ac_present_i),
    .pwrb_out_int(pwrb_out_int),
    .key0_out_int(key0_out_int),
    .key1_out_int(key1_out_int),
    .key2_out_int(key2_out_int),
    .bat_disable_int(bat_disable_int),
    .key_invert_ctl_i(reg2hw.key_invert_ctl),
    .pwrb_int(pwrb_int),
    .key0_int(key0_int),
    .key1_int(key1_int),
    .key2_int(key2_int),
    .ac_present_int(ac_present_int),
    .cio_bat_disable_o(cio_bat_disable_o),
    .cio_pwrb_out_o(cio_pwrb_out_o),
    .cio_key0_out_o(cio_key0_out_o),
    .cio_key1_out_o(cio_key1_out_o),
    .cio_key2_out_o(cio_key2_out_o)
  );

  //Instantiate the pin visibility and override module
  sysrst_ctrl_pin u_pin_vis_ovd (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .cio_pwrb_in_i(cio_pwrb_in_i),
    .cio_key0_in_i(cio_key0_in_i),
    .cio_key1_in_i(cio_key1_in_i),
    .cio_key2_in_i(cio_key2_in_i),
    .cio_ac_present_i(cio_ac_present_i),
    .cio_ec_rst_in_l_i(cio_ec_rst_in_l_i),
    .pwrb_out_hw(pwrb_out_hw),
    .key0_out_hw(key0_out_hw),
    .key1_out_hw(key1_out_hw),
    .key2_out_hw(key2_out_hw),
    .bat_disable_hw(bat_disable_hw),
    .ec_rst_l_hw(ec_rst_l_hw),
    .pin_allowed_ctl_i(reg2hw.pin_allowed_ctl),
    .pin_out_ctl_i(reg2hw.pin_out_ctl),
    .pin_out_value_i(reg2hw.pin_out_value),
    .pin_in_value_o(hw2reg.pin_in_value),
    .pwrb_out_int(pwrb_out_int),
    .key0_out_int(key0_out_int),
    .key1_out_int(key1_out_int),
    .key2_out_int(key2_out_int),
    .bat_disable_int(bat_disable_int),
    .cio_ec_rst_out_l_o(cio_ec_rst_out_l_o)
  );

  //Instantiate key-triggered interrupt module
  sysrst_ctrl_keyintr u_keyintr (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .pwrb_int(pwrb_int),
    .key0_int(key0_int),
    .key1_int(key1_int),
    .key2_int(key2_int),
    .ac_present_int(ac_present_int),
    .cio_ec_rst_in_l_i(cio_ec_rst_in_l_i),
    .key_intr_ctl_i(reg2hw.key_intr_ctl),
    .key_intr_debounce_ctl_i(reg2hw.key_intr_debounce_ctl),
    .key_intr_status_o(hw2reg.key_intr_status),
    .sysrst_ctrl_key_intr(sysrst_ctrl_key_intr)
  );

  //Instantiate combo module
  sysrst_ctrl_combo u_combo (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .pwrb_int(pwrb_int),
    .key0_int(key0_int),
    .key1_int(key1_int),
    .key2_int(key2_int),
    .ac_present_int(ac_present_int),
    .cio_ec_rst_in_l_i(cio_ec_rst_in_l_i),
    .ec_rst_ctl_i(reg2hw.ec_rst_ctl),
    .key_intr_debounce_ctl_i(reg2hw.key_intr_debounce_ctl),
    .com_sel_ctl_i(reg2hw.com_sel_ctl),
    .com_det_ctl_i(reg2hw.com_det_ctl),
    .com_out_ctl_i(reg2hw.com_out_ctl),
    .combo_intr_status_o(hw2reg.combo_intr_status),
    .sysrst_ctrl_combo_intr(sysrst_ctrl_combo_intr),
    .bat_disable_hw(bat_disable_hw),
    .gsc_rst_o(gsc_rst_o),
    .ec_rst_l_hw(ec_rst_l_hw)
  );

  // hardwire for now until logic is ready
  // see #6323
  assign gsc_wk_o = '0;

  //Instantiate the interrupt module
  sysrst_ctrl_intr u_intr (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .sysrst_ctrl_combo_intr(sysrst_ctrl_combo_intr),
    .sysrst_ctrl_key_intr(sysrst_ctrl_key_intr),
    .intr_state_i(reg2hw.intr_state),
    .intr_enable_i(reg2hw.intr_enable),
    .intr_test_i(reg2hw.intr_test),
    .intr_state_o(hw2reg.intr_state),
    .sysrst_ctrl_intr_o(intr_sysrst_ctrl_o)
  );

  // All outputs should be known value after reset
  `ASSERT_KNOWN(IntrSysRstCtrlOKnown, intr_sysrst_ctrl_o)
  // TODO: delete?
  //`ASSERT_KNOWN(GSCRstOKnown, gsc_rst_l_o)
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `ASSERT_KNOWN(BatOKnown, cio_bat_disable_o)
  `ASSERT_KNOWN(ECRSTOKnown, cio_ec_rst_out_l_o)
  `ASSERT_KNOWN(PwrbOKnown, cio_pwrb_out_o)
  `ASSERT_KNOWN(Key0OKnown, cio_key0_out_o)
  `ASSERT_KNOWN(Key1OKnown, cio_key1_out_o)
  `ASSERT_KNOWN(Key2OKnown, cio_key2_out_o)
  `ASSERT_KNOWN(BatOEnKnown, cio_bat_disable_en_o)
  `ASSERT_KNOWN(ECRSTOEnKnown, cio_ec_rst_out_l_en_o)
  `ASSERT_KNOWN(PwrbOEnKnown, cio_pwrb_out_en_o)
  `ASSERT_KNOWN(Key0OEnKnown, cio_key0_out_en_o)
  `ASSERT_KNOWN(Key1OEnKnown, cio_key1_out_en_o)
  `ASSERT_KNOWN(Key2OEnKnown, cio_key2_out_en_o)

endmodule
