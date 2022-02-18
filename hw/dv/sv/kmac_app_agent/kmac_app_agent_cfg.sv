// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual kmac_app_intf vif;

  int unsigned req_delay_min = 0;
  int unsigned req_delay_max = 1000;

  // delay between last for req data and done for digest data
  int unsigned rsp_delay_min = 0;
  int unsigned rsp_delay_max = 1000;

  // Enables/disable all protocol delays.
  rand bit zero_delays;

  // Enable starting the device auto-response sequence by default if configured in Device mode.
  bit start_default_device_seq = 1;

  // Knob to enable percentage of error response in auto-response sequence.
  int unsigned error_rsp_pct = 0;

  // Knob to allow injecting zeros in strb.
  bit inject_zero_in_host_strb = 0;

  rand push_pull_agent_cfg#(`CONNECT_DATA_WIDTH) m_data_push_agent_cfg;

  // KMAC digest share0/1 that can be set from test env.
  kmac_pkg::rsp_digest_t rsp_digest_hs[$];

  // Bias randomization in favor of enabling zero delays less often.
  constraint zero_delays_c {
    zero_delays dist { 0 := 8,
                       1 := 2 };
  }

  // Setter method for the user digest share queues - must be called externally to place specific user-digest_share0
  // to be sent by the driver.
  function void add_user_digest_share(kmac_pkg::rsp_digest_t rsp_digest_h);
    rsp_digest_hs.push_back(rsp_digest_h);
  endfunction
  // Getter method for the user digest share - returns the first data entry.
  function kmac_pkg::rsp_digest_t get_user_digest_share();
    `DV_CHECK_NE_FATAL(has_user_digest_share(), 0, "rsp_digest_share0 is empty!")
    return rsp_digest_hs.pop_front();
  endfunction
  // Getter method for the user digest share - must be called externally to check whether there is
  // any user data in the queues.
  function bit has_user_digest_share();
    return (rsp_digest_hs.size() > 0);
  endfunction

  `uvm_object_utils_begin(kmac_app_agent_cfg)
    `uvm_field_int(rsp_delay_min,            UVM_DEFAULT)
    `uvm_field_int(rsp_delay_max,            UVM_DEFAULT)
    `uvm_field_int(zero_delays,              UVM_DEFAULT)
    `uvm_field_int(start_default_device_seq, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
    m_data_push_agent_cfg = push_pull_agent_cfg#(`CONNECT_DATA_WIDTH)::type_id::create(
        "m_data_push_agent_cfg");
  endfunction : new

endclass
