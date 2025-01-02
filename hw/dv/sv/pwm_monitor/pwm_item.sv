// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_item extends uvm_sequence_item;

  int monitor_id    = 0; // for debugging purpose only
  int period        = 0; // clks in a pulse cycle
  int duty_cycle    = 0; // 0.16 fixed-point fraction for which output was asserted
  int active_cnt    = 0; // number of clocks pwm was asserted
  int inactive_cnt  = 0; // number of clocks pwm was deasserted
  int phase         = 0; // phase at which output was asserted (0-ffff)
  bit invert        = 0; // (1) active low (0) active high

  // May be assigned to `phase` to indicate that the pwm phase cannot be ascertained because
  // the signal has never been asserted.
  static int PhaseUnknown = -1;

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
      txt = { txt, $sformatf("\n Duty cycle %04x", duty_cycle) };
      txt = { txt, $sformatf("\n inverted %0b", invert) };
      txt = { txt, $sformatf("\n # of active cycles %d", active_cnt) };
      txt = { txt, $sformatf("\n # of inactive cycles %d", inactive_cnt) };
      txt = { txt, $sformatf("\n phase cnt %d", phase) };
      return txt;
    endfunction : convert2string

  function int get_duty_cycle();
    // 16-bit fraction for which the duty cycle is asserted; 0xffff nearly always asserted;
    // the DUT cannot produce a continuously asserted output except by using inversion and
    // a duty cycle of 0.
    return (active_cnt << 16) / period;
  endfunction : get_duty_cycle
endclass
