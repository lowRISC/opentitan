// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_item extends uvm_sequence_item;

  // random variables

   bit ac_present;
   rand bit key0_in;
   rand bit key1_in;
   rand bit key2_in;
   rand bit pwrb_in;
   rand bit lid_open;
   bit ec_rst_l_in;

   //output pins
   bit bat_disable;
   bit flash_wp_l;
   bit key0_out;
   bit key1_out;
   bit key2_out;
   bit pwrb_out;
   bit z3_wakeup;

  `uvm_object_utils_begin(sysrst_ctrl_item)
    `uvm_field_int(ac_present, UVM_ALL_ON)
    `uvm_field_int(key0_in, UVM_ALL_ON)
    `uvm_field_int(key1_in, UVM_ALL_ON)
    `uvm_field_int(key2_in, UVM_ALL_ON)
    `uvm_field_int(pwrb_in, UVM_ALL_ON)
    `uvm_field_int(lid_open, UVM_ALL_ON)
    `uvm_field_int(ec_rst_l_in, UVM_ALL_ON)
  `uvm_object_utils_end

  `uvm_object_new

endclass
