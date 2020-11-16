// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual keymgr_kmac_intf vif;

  // delay between last for req data and done for digest data
  int unsigned rsp_delay_min = 0;
  int unsigned rsp_delay_max = 1000;

  // Enables/disable all protocol delays.
  rand bit zero_delays;

  // Enable starting the device auto-response sequence by default if configured in Device mode.
  bit start_default_device_seq = 1;

  // Bias randomization in favor of enabling zero delays less often.
  constraint zero_delays_c {
    zero_delays dist { 0 := 8,
                       1 := 2 };
  }

  push_pull_agent_cfg#(`CONNECT_DATA_WIDTH) m_data_push_agent_cfg;

  `uvm_object_utils_begin(keymgr_kmac_agent_cfg)
    `uvm_field_int(rsp_delay_min,            UVM_DEFAULT)
    `uvm_field_int(rsp_delay_max,            UVM_DEFAULT)
    `uvm_field_int(zero_delays,              UVM_DEFAULT)
    `uvm_field_int(start_default_device_seq, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
