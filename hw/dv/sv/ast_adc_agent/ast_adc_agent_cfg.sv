// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual ast_adc_if vif;

  // Minimum and maximum response delays
  rand int unsigned resp_dly_min = 0;
  rand int unsigned resp_dly_max = 25;

  `uvm_object_utils_begin(ast_adc_agent_cfg)
    `uvm_field_int(resp_dly_min, UVM_DEFAULT)
    `uvm_field_int(resp_dly_min, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  // Defaults 
  constraint defaults_c {
    soft resp_dly_min == 0;
    soft resp_dly_max == 25;
  }
endclass
