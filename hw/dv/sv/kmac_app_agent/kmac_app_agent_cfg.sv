// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_agent_cfg extends dv_reactive_agent_cfg;
  // Handle to the agent's interface
  virtual kmac_app_if vif;

  // Used in Device mode. The maximum length of time that the device is not ready when it is not
  // processing a request.
  int unsigned max_idle_time_not_ready = 8;

  // Used in Device mode. The percentage chance for the device to be ready to receive a request on a
  // cycle (assuming the device is idle and there haven't already been max_idle_time_not_ready
  // cycles of not being ready)
  int unsigned idle_ready_pct = 50;

  // Bounds used by the host sequence for the m_delay value in the kmac_app_req_item objects it
  // generates. This is the number of cycles to wait before sending the request.
  int unsigned req_delay_min = 0;
  int unsigned req_delay_max = 10;

  // Bounds used by the device sequence for the number of cycles between when a request is accepted
  // and when a response is sent.
  int unsigned rsp_delay_min = 0;
  int unsigned rsp_delay_max = 100;

  // If this is set then the device and response sequence will both constrain delays to be zero.
  rand bit zero_delays;

  // Knob to enable percentage of error response in auto-response sequence.
  int unsigned error_rsp_pct = 0;

  // Knob to control whether a response where a share is '0 or '1 is considered an error response
  bit constant_share_means_error = 1'b1;

  // Knob to allow injecting zeros in strb.
  bit inject_zero_in_host_strb = 0;

  // A queue of digest responses. If the agent is in Device mode, this can be filled by calling
  // add_user_digest. Once that has been done, the automatic device-mode sequence will respond the
  // data in this queue.
  rsp_digest_t rsp_digest_hs[$];

  extern function new (string name = "");

  // Add a digest to the user digest queue.
  //
  // This only makes sense in Device mode.
  extern function void add_user_digest(rsp_digest_t rsp_digest_h);

  // Pop the first item from the user digest queue. This will fail with an error if the queue is
  // empty.
  extern function rsp_digest_t pop_user_digest();

  // Returns true if the user digest queue is nonempty
  extern function bit has_user_digest();

  `uvm_object_utils_begin(kmac_app_agent_cfg)
    `uvm_field_int(req_delay_min,            UVM_DEFAULT)
    `uvm_field_int(req_delay_max,            UVM_DEFAULT)
    `uvm_field_int(rsp_delay_min,            UVM_DEFAULT)
    `uvm_field_int(rsp_delay_max,            UVM_DEFAULT)
    `uvm_field_int(zero_delays,              UVM_DEFAULT)
  `uvm_object_utils_end

  // Bias randomization in favor of enabling zero delays less often.
  extern constraint zero_delays_c;
endclass

function kmac_app_agent_cfg::new (string name = "");
  super.new(name);
endfunction : new

function void kmac_app_agent_cfg::add_user_digest(rsp_digest_t rsp_digest_h);
  if (if_mode != Device) begin
    `uvm_fatal(get_name(), $sformatf("Cannot add a digest: agent is in %0s mode.", if_mode.name()))
  end

  rsp_digest_hs.push_back(rsp_digest_h);
endfunction

function rsp_digest_t kmac_app_agent_cfg::pop_user_digest();
  if (!has_user_digest()) begin
    `uvm_fatal(get_name(), "Cannot get a user digest: the queue is empty.")
  end
  return rsp_digest_hs.pop_front();
endfunction

function bit kmac_app_agent_cfg::has_user_digest();
  return (rsp_digest_hs.size() > 0);
endfunction

constraint kmac_app_agent_cfg::zero_delays_c {
  zero_delays dist { 0 := 8, 1 := 2 };
}
