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
  logic lid_open;
  logic bat_disable;
  logic flash_wp_l;
  logic ec_rst_l_out;
  logic key0_out;
  logic key1_out;
  logic key2_out;
  logic pwrb_out;
  logic z3_wakeup;
  logic z3_wakeup_in;
  logic bat_disable_in;
  logic ac_present_out;
  logic lid_open_out;

  // reset value of input signals
  function automatic void reset_signals();
    ac_present <= 0;
    key0_in <= 0;
    key1_in <= 0;
    key2_in <= 0;
    pwrb_in <= 0;
    lid_open <= 0;
    ec_rst_l_in <= 1;
    z3_wakeup_in <= 0;
    bat_disable_in <= 0;
  endfunction

  task automatic randomize_input();
    // VCS doesn't support randomizing logic variable
    // so declare bit variable, randomize it and assigned it to logic
    bit pwrb, key0, key1, key2, ec_rst_l;
    `DV_CHECK_FATAL(std::randomize(pwrb, key0, key1, key2, ec_rst_l), ,
       "sysrst_ctrl_if")
    pwrb_in = pwrb;
    key0_in = key0;
    key1_in = key1;
    key2_in = key2;
    ec_rst_l_in = ec_rst_l;
  endtask

endinterface : sysrst_ctrl_if
