// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Configuration class for Alert agent
// ---------------------------------------------
class alert_esc_agent_cfg extends dv_base_agent_cfg;
  virtual alert_esc_if vif;
  virtual alert_esc_probe_if probe_vif;
  bit is_alert        = 1;
  bit is_async        = 0;
  bit en_ping_cov     = 1;
  bit en_lpg_cov      = 1;
  bit alert_init_done = 0;
  bit en_alert_lpg    = 0;

  // Enabled via plusarg.
  // Please only use this plusarg in top-level test.
  // For IP level test, please set `exp_fatal_alert` in post_start() instead.
  bit bypass_alert_ready_to_end_check = 0;

  bit bypass_esc_ready_to_end_check = 0;

  // When this flag is set to 1, and agent in alert host mode, the sequence will automatically
  // response to alert ping requests.
  bit start_default_rsp_seq = 1;

  // Control if ping response will timeout or not.
  bit ping_timeout = 0;

  // Monitor will set this value to 1 when the agent is under ping handshake.
  bit under_ping_handshake = 0;

  // dut clk frequency, used to generate alert async_clk frequency
  int clk_freq_mhz;

  // sender mode
  bit use_seq_item_alert_delay;
  int unsigned alert_delay_min = 0;
  int unsigned alert_delay_max = 10;

  // receiver mode
  bit use_seq_item_ack_delay;
  int unsigned ack_delay_min = 0;
  int unsigned ack_delay_max = 10;

  bit use_seq_item_ack_stable;
  int unsigned ack_stable_min = 0;
  int unsigned ack_stable_max = 10;

  bit use_seq_item_ping_delay;
  int unsigned ping_delay_min = 0;
  int unsigned ping_delay_max = 10;

  // When this bit is set, alert agent responds to alert without delay
  // This is set by plusarg "+fast_rcvr_{alert_name}"
  bit          fast_rcvr = 0;
  // this timeout is to ensure handshake protocol did not hang, this timeout is not implemented in
  // design. In design, if protocol hangs, the period ping check will catch the issue
  int unsigned handshake_timeout_cycle = 100_000;
  int unsigned ping_timeout_cycle = 32;

  bit under_reset;

  `uvm_object_utils_begin(alert_esc_agent_cfg)
    `uvm_field_int(alert_delay_min, UVM_DEFAULT)
    `uvm_field_int(alert_delay_max, UVM_DEFAULT)
    `uvm_field_int(ack_delay_min,   UVM_DEFAULT)
    `uvm_field_int(ack_delay_max,   UVM_DEFAULT)
    `uvm_field_int(ack_stable_min,  UVM_DEFAULT)
    `uvm_field_int(ack_stable_max,  UVM_DEFAULT)
    `uvm_field_int(ping_delay_min,  UVM_DEFAULT)
    `uvm_field_int(ping_delay_max,  UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  function bit get_esc_en();
    if (if_mode == Device && is_active) begin
      return probe_vif.get_esc_en();
    end
    // Only support escalation ping request interrupted by real escalation request in device mode.
    return 0;
  endfunction

endclass : alert_esc_agent_cfg
