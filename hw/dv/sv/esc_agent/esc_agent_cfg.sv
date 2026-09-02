// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class esc_agent_cfg extends dv_reactive_agent_cfg;
  virtual esc_if vif;
  virtual esc_probe_if probe_vif;

  bit is_async        = 0;
  bit en_ping_cov     = 1;
  bit en_lpg_cov      = 1;

  // Enabled via plusarg.
  // Please only use this plusarg in top-level test.
  bit bypass_esc_ready_to_end_check = 0;

  // Control if ping response will timeout or not.
  bit ping_timeout = 0;

  // Monitor will set this value to 1 when the agent is under ping handshake.
  bit under_ping_handshake = 0;

  // Monitor will set this value to 1 when the agent is under ping handshake phase 2.
  bit under_ping_handshake_ph_2 = 0;

  // dut clk frequency, used to generate alert async_clk frequency
  int clk_freq_mhz;

  // receiver mode
  int unsigned ack_delay_min = 0;
  int unsigned ack_delay_max = 10;

  int unsigned ack_stable_min = 0;
  int unsigned ack_stable_max = 10;

  // this timeout is to ensure handshake protocol did not hang, this timeout is not implemented in
  // design. In design, if protocol hangs, the period ping check will catch the issue
  int unsigned handshake_timeout_cycle = 100_000;
  int unsigned ping_timeout_cycle = 32;

  // Incremented by the monitor on each ping
  int unsigned ping_count = 0;

  `uvm_object_utils_begin(esc_agent_cfg)
    `uvm_field_int(ack_delay_min,   UVM_DEFAULT)
    `uvm_field_int(ack_delay_max,   UVM_DEFAULT)
    `uvm_field_int(ack_stable_min,  UVM_DEFAULT)
    `uvm_field_int(ack_stable_max,  UVM_DEFAULT)
  `uvm_object_utils_end

  extern function new (string name="");
  extern function bit get_esc_en();

endclass : esc_agent_cfg

function esc_agent_cfg::new (string name="");
  super.new(name);
endfunction : new

function bit esc_agent_cfg::get_esc_en();
  if (if_mode == Device && is_active) begin
    return probe_vif.get_esc_en();
  end
  // Only support escalation ping request interrupted by real escalation request in device mode.
  return 0;
endfunction
