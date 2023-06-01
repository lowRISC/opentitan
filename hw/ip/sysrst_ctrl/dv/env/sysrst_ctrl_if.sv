// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sysrst_ctrl_if (
  input logic clk_i,
  input logic rst_ni
);

  logic key0_in;
  logic key1_in;
  logic key2_in;
  logic pwrb_in;
  logic ac_present;
  logic ec_rst_l_in;
  logic flash_wp_l_in;
  logic lid_open;
  logic bat_disable;
  logic flash_wp_l;
  logic ec_rst_l_out;
  logic key0_out;
  logic key1_out;
  logic key2_out;
  logic pwrb_out;
  logic z3_wakeup;
  logic rst_req;
  logic wkup_req;

  logic [6:0] sysrst_ctrl_inputs;
  logic [7:0] sysrst_ctrl_inputs_int;

  `ifndef SYSRST_CTRL_DUT_TOP
  `define SYSRST_CTRL_DUT_TOP tb.dut
  `endif

  // reset value of input signals
  function automatic void reset_signals();
    ac_present <= 0;
    key0_in <= 0;
    key1_in <= 0;
    key2_in <= 0;
    pwrb_in <= 0;
    lid_open <= 0;
    ec_rst_l_in <= 1;
    flash_wp_l_in <= 1;
  endfunction


  task automatic randomize_input();
    // VCS doesn't support randomizing logic variable
    // so declare bit variable, randomize it and assigned it to logic
    bit pwrb, key0, key1, key2, ec_rst_l, ac_prst, ld_op, flash_wp;
    `DV_CHECK_FATAL(std::randomize(pwrb, key0, key1, key2, ec_rst_l, ac_prst, ld_op, flash_wp), ,
       "sysrst_ctrl_if")
    pwrb_in = pwrb;
    key0_in = key0;
    key1_in = key1;
    key2_in = key2;
    ac_present = ac_prst;
    lid_open = ld_op;
    ec_rst_l_in = ec_rst_l;
    flash_wp_l_in = flash_wp;
  endtask

  task automatic randomize_combo_input(bit[4:0] mask=5'h1F);
    // VCS doesn't support randomizing logic variable
    // so declare bit variable, randomize it and assigned it to logic
    bit pwrb, key0, key1, key2, ac_prst;
    `DV_CHECK_FATAL(std::randomize(pwrb, key0, key1, key2, ac_prst), ,
       "sysrst_ctrl_if")
    if(mask[0]) key0_in = key0;
    if(mask[1]) key1_in = key1;
    if(mask[2]) key2_in = key2;
    if(mask[3]) pwrb_in = pwrb;
    if(mask[4]) ac_present = ac_prst;
  endtask

  assign sysrst_ctrl_inputs = {flash_wp_l_in, ec_rst_l_in, ac_present, key2_in, key1_in, key0_in,
                               pwrb_in};
  assign sysrst_ctrl_inputs_int[0] = `SYSRST_CTRL_DUT_TOP.aon_pwrb_int;
  assign sysrst_ctrl_inputs_int[1] = `SYSRST_CTRL_DUT_TOP.aon_key0_int;
  assign sysrst_ctrl_inputs_int[2] = `SYSRST_CTRL_DUT_TOP.aon_key1_int;
  assign sysrst_ctrl_inputs_int[3] = `SYSRST_CTRL_DUT_TOP.aon_key2_int;
  assign sysrst_ctrl_inputs_int[4] = `SYSRST_CTRL_DUT_TOP.aon_ac_present_int;
  assign sysrst_ctrl_inputs_int[5] = `SYSRST_CTRL_DUT_TOP.aon_ec_rst_l_int;
  assign sysrst_ctrl_inputs_int[6] = `SYSRST_CTRL_DUT_TOP.aon_flash_wp_l_int;
  assign sysrst_ctrl_inputs_int[7] = `SYSRST_CTRL_DUT_TOP.aon_lid_open_int;

endinterface : sysrst_ctrl_if
