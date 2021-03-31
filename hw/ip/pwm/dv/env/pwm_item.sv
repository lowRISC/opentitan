// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_item extends uvm_sequence_item;
  int  en_cycles;
  int  duty_cycle;

  `uvm_object_utils_begin(pwm_item)
    `uvm_field_int(en_cycles,  UVM_DEFAULT)
    `uvm_field_int(duty_cycle, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void reset();
    en_cycles  = 0;
    duty_cycle = 0;
  endfunction : reset
endclass : pwm_item
