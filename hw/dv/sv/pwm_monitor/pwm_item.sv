// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_item extends uvm_sequence_item;
  int  duty_high;
  int  duty_low;
  int  index;

  `uvm_object_utils_begin(pwm_item)
    `uvm_field_int(index,     UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_int(duty_high, UVM_DEFAULT)
    `uvm_field_int(duty_low,  UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : pwm_item
