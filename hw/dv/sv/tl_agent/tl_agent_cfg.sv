// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Configuration class for TileLink agent
// ---------------------------------------------
class tl_agent_cfg extends uvm_object;

  // TileLink conformance level supported by this agent
  // Right now only TL-UL is supported
  tl_level_e tl_level = kTLUL;

  // Maximum outstanding transaction
  // 0: Unlimited from the master perspective, might be back-pressured by the slave
  // 1: Only single transaction at a time
  // n: Number of maximum oustanding requests
  int unsigned max_outstanding_req = 1; // most of IPs only support 1 outstanding req

  // TileLink channel valid delay (host mode)
  bit use_seq_item_a_valid_delay;
  int unsigned a_valid_delay_min = 0;
  int unsigned a_valid_delay_max = 10;

  // TileLink channel ready delay (host mode)
  int unsigned d_ready_delay_min = 0;
  int unsigned d_ready_delay_max = 10;

  // TileLink channel ready delay (device mode)
  int unsigned a_ready_delay_min = 0;
  int unsigned a_ready_delay_max = 10;

  // TileLink channel ready delay (device mode)
  bit use_seq_item_d_valid_delay;
  int unsigned d_valid_delay_min = 0;
  int unsigned d_valid_delay_max = 10;

  // Agent mode:  host and device
  bit is_host = 1;
  bit is_active = 1;

  `uvm_object_utils_begin(tl_agent_cfg)
    `uvm_field_int(max_outstanding_req,   UVM_DEFAULT)
    `uvm_field_enum(tl_level_e, tl_level, UVM_DEFAULT)
    `uvm_field_int(is_host,               UVM_DEFAULT)
    `uvm_field_int(is_active,             UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_max,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_max,     UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
  endfunction : new

endclass
