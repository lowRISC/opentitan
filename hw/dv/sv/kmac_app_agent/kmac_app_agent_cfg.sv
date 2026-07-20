// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_agent_cfg extends dv_reactive_agent_cfg;

  // Interface handle used by driver, monitor and the sequencer
  virtual kmac_app_intf vif;

  // Minimum and maximum delays between requests
  int unsigned req_delay_min = 0;
  int unsigned req_delay_max = 100;

  // Minimum and maximum delays between last message request and first digest response
  int unsigned rsp_delay_min = 0;
  int unsigned rsp_delay_max = 100;

  // If this is set, all protocol delays will be zero.
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

  // Configuration for the push_pull_agent that is being used to implement the kmac_app_agent.
  rand push_pull_agent_cfg#(`CONNECT_DATA_WIDTH) m_data_push_agent_cfg;

  // KMAC digest share0/1 that can be set from test env.
  kmac_pkg::rsp_digest_t rsp_digest_hs[$];

  extern function new (string name = "");

  // Add the given digest to the queue.
  extern function void add_user_digest(kmac_pkg::rsp_digest_t rsp_digest_h);

  // Pop the first digest from the queue. Generate an error if there is none.
  extern function kmac_pkg::rsp_digest_t pop_user_digest();

  // Return true if there is at least one digest in the queue.
  extern function bit has_user_digest();

  // Bias randomization in favor of enabling zero delays less often.
  extern constraint zero_delays_c;

  `uvm_object_utils_begin(kmac_app_agent_cfg)
    `uvm_field_int(rsp_delay_min,            UVM_DEFAULT)
    `uvm_field_int(rsp_delay_max,            UVM_DEFAULT)
    `uvm_field_int(zero_delays,              UVM_DEFAULT)
    `uvm_field_int(start_default_device_seq, UVM_DEFAULT)
  `uvm_object_utils_end
endclass

function kmac_app_agent_cfg::new (string name = "");
  super.new(name);
  m_data_push_agent_cfg = push_pull_agent_cfg#(`CONNECT_DATA_WIDTH)::type_id::create(
      "m_data_push_agent_cfg");
endfunction : new

function void kmac_app_agent_cfg::add_user_digest(kmac_pkg::rsp_digest_t rsp_digest_h);
  rsp_digest_hs.push_back(rsp_digest_h);
endfunction

function kmac_pkg::rsp_digest_t kmac_app_agent_cfg::pop_user_digest();
  if (!has_user_digest()) begin
    `uvm_fatal(get_name(), "Cannot get a user digest: the queue is empty.")
  end
  return rsp_digest_hs.pop_front();
endfunction

function bit kmac_app_agent_cfg::has_user_digest();
  return (rsp_digest_hs.size() > 0);
endfunction

constraint kmac_app_agent_cfg::zero_delays_c {
  zero_delays dist { 0 := 8,
                     1 := 2 };
}
