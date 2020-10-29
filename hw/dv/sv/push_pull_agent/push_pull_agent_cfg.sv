// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_agent_cfg #(parameter int HostDataWidth = 32,
                            parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual push_pull_if#(HostDataWidth, DeviceDataWidth) vif;

  // Determines whether this agent is configured as push or pull.
  // Should be set from the IP level environment.
  push_pull_agent_e agent_type;

  // Configures the agent to act in bidirectional mode,
  // transferring data on both sides of the handshake.
  bit in_bidirectional_mode = 1'b0;

  // Device-side delay range for both Push/Pull protocols.
  int unsigned device_delay_min = 0;
  int unsigned device_delay_max = 10;

  // Host-side delay range for both Push/Pull protocols.
  int unsigned host_delay_min = 0;
  int unsigned host_delay_max = 10;

  // Enables/disable all protocol delays.
  rand bit zero_delays;

  // Enable starting the device sequence by default if configured in Device mode.
  bit start_default_device_seq = 1;

  // Bias randomization in favor of enabling zero delays less often.
  constraint zero_delays_c {
    zero_delays dist { 0 := 7,
                       1 := 3 };
  }

  `uvm_object_param_utils_begin(push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth))
    `uvm_field_enum(push_pull_agent_e, agent_type, UVM_DEFAULT)
    `uvm_field_int(in_bidirectional_mode,          UVM_DEFAULT)
    `uvm_field_int(device_delay_min,               UVM_DEFAULT)
    `uvm_field_int(device_delay_max,               UVM_DEFAULT)
    `uvm_field_int(host_delay_min,                 UVM_DEFAULT)
    `uvm_field_int(host_delay_max,                 UVM_DEFAULT)
    `uvm_field_int(zero_delays,                    UVM_DEFAULT)
    `uvm_field_int(start_default_device_seq,       UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
