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
    bit pwrb, key0, key1, key2, ec_rst_l, ac_pst, ld_op, flash_wp;
    `DV_CHECK_FATAL(std::randomize(pwrb, key0, key1, key2, ec_rst_l, ac_pst, ld_op, flash_wp), ,
       "sysrst_ctrl_if")
    pwrb_in = pwrb;
    key0_in = key0;
    key1_in = key1;
    key2_in = key2;
    ac_present = ac_pst;
    lid_open = ld_op;
    ec_rst_l_in = ec_rst_l;
    flash_wp_l_in = flash_wp;
  endtask

endinterface : sysrst_ctrl_if
