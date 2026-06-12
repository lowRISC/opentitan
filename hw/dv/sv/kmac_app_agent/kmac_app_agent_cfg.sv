// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_agent_cfg extends dv_reactive_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual kmac_app_intf vif;

  int unsigned req_delay_min = 0;
  int unsigned req_delay_max = 100;

  // delay between last message request and first digest response
  int unsigned rsp_delay_min = 0;
  int unsigned rsp_delay_max = 100;

  // Enables/disable all protocol delays.
  rand bit zero_delays;

  // Enable starting the device auto-response sequence by default if configured in Device mode.
  bit start_default_device_seq = 1;

  // Knob to enable percentage of error response in auto-response sequence.
  int unsigned error_rsp_pct = 0;

  // Knob to control whether an error response can be caused by all zeros or all ones in one of the
  // shares.
  bit constant_share_means_error = 1'b1;

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

  // Setter method, which adds the given digest to the queue.
  function void add_user_digest(kmac_pkg::rsp_digest_t rsp_digest_h);
    rsp_digest_hs.push_back(rsp_digest_h);
  endfunction

  // Getter method for the user digest. Returns the first digest, or an error if there is none.
  function kmac_pkg::rsp_digest_t pop_user_digest();
    if (!has_user_digest()) begin
      `uvm_fatal(get_name(), "Cannot get a user digest: the queue is empty.")
    end
    return rsp_digest_hs.pop_front();
  endfunction

  // Getter method that returns true if there is at least one digest in the queue.
  function bit has_user_digest();
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
