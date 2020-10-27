// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_agent_cfg extends dv_base_agent_cfg;
  bit en_monitor = 1'b1;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual pattgen_if vif;

  bit polarity_ch0;
  bit polarity_ch1;

  `uvm_object_utils_begin(pattgen_agent_cfg)
    `uvm_field_int(polarity_ch0, UVM_DEFAULT)
    `uvm_field_int(polarity_ch1, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : pattgen_agent_cfg
