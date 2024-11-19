// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_item extends uvm_sequence_item;
  int unsigned active_cnt    = 0; // number of clocks pwm was high
  int unsigned inactive_cnt  = 0; // number of clocks pwm was low
  int unsigned phase         = 0; // what clock cnt did the pulse start
  bit invert                 = 0; // (1)active low (0) active high

  `uvm_object_utils_begin(pwm_item)
    `uvm_field_int(active_cnt, UVM_DEFAULT)
    `uvm_field_int(inactive_cnt, UVM_DEFAULT)
    `uvm_field_int(phase, UVM_DEFAULT)
    `uvm_field_int(invert, UVM_DEFAULT)
  `uvm_object_utils_end

  extern function new (string name="");
  extern function string convert2string();

  // Return the total time taken by the item (active and inactive cycles)
  extern function int unsigned get_period();

  // Return the duty cycle as a rounded percentage
  extern function int unsigned get_duty_cycle();
endclass

function pwm_item::new (string name="");
  super.new(name);
endfunction

function string pwm_item::convert2string();
  string txt ="";
  txt = "\n------| PWM ITEM |------";
  txt = { txt, $sformatf("\n inverted %0b", invert) };
  txt = { txt, $sformatf("\n # of active cycles %d", active_cnt) };
  txt = { txt, $sformatf("\n # of inactive cycles %d", inactive_cnt) };
  txt = { txt, $sformatf("\n phase cnt %d", phase) };
  return txt;
endfunction

function int unsigned pwm_item::get_period();
  return active_cnt + inactive_cnt;
endfunction

function int pwm_item::get_duty_cycle();
  int high_cnt = invert ? inactive_cnt : active_cnt;
  return real'(high_cnt) / real'(get_period()) * 100;
endfunction
