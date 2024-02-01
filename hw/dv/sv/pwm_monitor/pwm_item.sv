// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_item extends uvm_sequence_item;

  int monitor_id    = 0; // for debugging purpose only
  int period        = 0; // clks in a beat
  int duty_cycle    = 0; // high vs low cnt
  int active_cnt    = 0; // number of clocks pwm was high
  int inactive_cnt  = 0; // number of clocks pwm was low
  int phase         = 0; // what clock cnt did the pulse start
  bit invert        = 0; // (1)active low (0) active high

  `uvm_object_utils_begin(pwm_item)
    `uvm_field_int(period, UVM_DEFAULT)
    `uvm_field_int(duty_cycle, UVM_DEFAULT)
    `uvm_field_int(active_cnt, UVM_DEFAULT)
    `uvm_field_int(inactive_cnt, UVM_DEFAULT)
    `uvm_field_int(phase, UVM_DEFAULT)
    `uvm_field_int(invert, UVM_DEFAULT)
    `uvm_field_int(monitor_id, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

    function string convert2string();
      string txt ="";
      txt = "\n------| PWM ITEM |------";
      txt = { txt, $sformatf("\n Item from monitor %d", monitor_id) };
      txt = { txt, $sformatf("\n Period %d clocks", period) };
      txt = { txt, $sformatf("\n Duty cycle %0d pct ", duty_cycle) };
      txt = { txt, $sformatf("\n inverted %0b", invert) };
      txt = { txt, $sformatf("\n # of active cycles %d", active_cnt) };
      txt = { txt, $sformatf("\n # of inactive cycles %d", inactive_cnt) };
      txt = { txt, $sformatf("\n phase cnt %d", phase) };
      return txt;
    endfunction : convert2string

  function int get_duty_cycle();
    real dc = 0;
    dc = (invert) ? (real'(inactive_cnt) / real'(period) * 100)
                  : (real'(active_cnt) / real'(period) * 100);
    return dc;
  endfunction : get_duty_cycle
endclass
