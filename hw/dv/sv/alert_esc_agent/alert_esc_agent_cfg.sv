// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Configuration class for Alert agent
// ---------------------------------------------
class alert_esc_agent_cfg extends dv_base_agent_cfg;
  virtual alert_esc_if vif;
  virtual alert_esc_probe_if probe_vif;
  bit is_alert     = 1;
  bit is_async     = 0;
  bit en_ping_cov  = 1;
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

  // this timeout is to ensure handshake protocol did not hang, this timeout is not implemented in
  // design. In design, if protocol hangs, the period ping check will catch the issue
  int unsigned handshake_timeout_cycle = 100_000;
  int unsigned ping_timeout_cycle = 32;

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

endclass : alert_esc_agent_cfg
