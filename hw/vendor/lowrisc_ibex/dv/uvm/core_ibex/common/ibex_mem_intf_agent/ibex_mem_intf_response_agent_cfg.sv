// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_response_agent_cfg
//------------------------------------------------------------------------------

class ibex_mem_intf_response_agent_cfg extends uvm_object;

  // interface handle used by driver & monitor
  virtual ibex_mem_intf vif;

  // When set write responses have a fixed 32'hffffffff for rdata and matching correct rintg. When
  // unset both rdata and rintg fields are x for write responses
  bit fixed_data_write_response = 1'b0;

  // delay between request and grant
  int unsigned gnt_delay_min = 0;
  int unsigned gnt_delay_max = 10;
  // Pick the weight assigned to choosing medium and long gaps between request and grant
  int unsigned gnt_pick_medium_speed_weight = 1;
  int unsigned gnt_pick_slow_speed_weight = 1;

  // delay between grant and rvalid
  int unsigned valid_delay_min = 0;
  int unsigned valid_delay_max = 20;
  // Pick the weight assigned to choosing medium and long gaps between grant and rvalid
  int unsigned valid_pick_medium_speed_weight = 1;
  int unsigned valid_pick_slow_speed_weight = 1;

  // Enables/disable all protocol delays.
  rand bit zero_delays;

  // Knob to enable percentage of zero delay in auto-response sequence.
  // Default set to 50% for zero delay to be picked
  int unsigned zero_delay_pct = 50;

  // CONTROL_KNOB : enable/disable to generation of bad integrity upon uninit accesses
  bit enable_bad_intg_on_uninit_access = 0;

  constraint zero_delays_c {
    zero_delays dist {1 :/ zero_delay_pct,
                      0 :/ 100 - zero_delay_pct};
  }

  `uvm_object_utils_begin(ibex_mem_intf_response_agent_cfg)
    `uvm_field_int(fixed_data_write_response, UVM_DEFAULT)
    `uvm_field_int(gnt_delay_min,             UVM_DEFAULT)
    `uvm_field_int(gnt_delay_max,             UVM_DEFAULT)
    `uvm_field_int(valid_delay_min,           UVM_DEFAULT)
    `uvm_field_int(valid_delay_max,           UVM_DEFAULT)
    `uvm_field_int(zero_delays,               UVM_DEFAULT)
    `uvm_field_int(zero_delay_pct,            UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction

endclass
