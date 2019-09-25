// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  // random variables
  //rand i2c_bit_type_t  bit_type = 1'b0;
  rand bit             sda_bit = 1'b1;
  rand bit             scl_bit = 1'b1;

  rand bit             stop_detected = 1'b0;
  rand bit             start_detected = 1'b0;

  // dont override start_bit unless testing an error scenario
  constraint sda_bit_c {
    sda_bit == 1'b1;
  }

  // dont override stop_bit unless testing an error scenario
  constraint scl_bit_c {
    sda_bit == 1'b1;
  }

  `uvm_object_utils_begin(i2c_item)
    `uvm_field_int(sda_bit,       UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(scl_bit,       UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_item
