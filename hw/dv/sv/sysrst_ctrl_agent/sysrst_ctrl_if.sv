// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sysrst_ctrl_if (
   input logic clk_i,
   input logic rst_ni
);
  // interface pins

   logic ac_present;
   logic ec_rst_l_in;
   logic key0_in;
   logic key1_in;
   logic key2_in;
   logic pwrb_in;
   logic lid_open;
   logic bat_disable;
   logic flash_wp_l;
   logic ec_rst_l_out;
   logic key0_out;
   logic key1_out;
   logic key2_out;
   logic pwrb_out;
   logic z3_wakeup;

   clocking driver_cb @(posedge clk_i);
    input rst_ni;
    output ac_present;
    output ec_rst_l_in;
    output key0_in;
    output key1_in;
    output key2_in;
    output pwrb_in;
    output lid_open;
    input bat_disable;
    input flash_wp_l;
    input ec_rst_l_out;
    input key0_out;
    input key1_out;
    input key2_out;
    input pwrb_out;
    input z3_wakeup;
   endclocking

   clocking monitor_cb @(posedge clk_i);
    input rst_ni;
    input ac_present;
    inout ec_rst_l_in;
    input key0_in;
    input key1_in;
    input key2_in;
    input pwrb_in;
    input lid_open;
    input bat_disable;
    input flash_wp_l;
    input ec_rst_l_out;
    input key0_out;
    input key1_out;
    input key2_out;
    input pwrb_out;
    input z3_wakeup;
   endclocking

   
endinterface :sysrst_ctrl_if
