// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_agent_cfg extends dv_base_agent_cfg;
  bit en_monitor = 1'b1; // enable monitor

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual pattgen_if vif;

  bit [NUM_PATTGEN_CHANNELS-1:0] error_injected;

  bit  polarity[NUM_PATTGEN_CHANNELS-1:0];
  uint length[NUM_PATTGEN_CHANNELS-1:0];

  `uvm_object_utils_begin(pattgen_agent_cfg)
    `uvm_field_int(error_injected,  UVM_DEFAULT)
    `uvm_field_sarray_int(polarity, UVM_DEFAULT)
    `uvm_field_sarray_int(length,   UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : pattgen_agent_cfg
