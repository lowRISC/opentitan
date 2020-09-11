// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Configuration class for TileLink agent
// ---------------------------------------------
class tl_agent_cfg extends dv_base_agent_cfg;

  virtual tl_if  vif;
  // TileLink conformance level supported by this agent
  // Right now only TL-UL is supported
  tl_level_e tl_level = kTLUL;

  // Maximum outstanding transaction
  // 0: Unlimited from the host perspective, might be back-pressured by the device
  // 1: Only single transaction at a time
  // n: Number of maximum oustanding requests

  // Set for this large value to find max outstanding req DV can hit
  // Then compare this value with designers to check if it meets their expectation
  int unsigned max_outstanding_req = 16;


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

  // make a fifo with available req IDs
  rand int unsigned outstanding_req_fifo[$];

  constraint c_outstanding_req_fifo {
    outstanding_req_fifo.size() == max_outstanding_req;
    unique{outstanding_req_fifo};
    foreach(outstanding_req_fifo[i])
       outstanding_req_fifo[i] inside {[0:max_outstanding_req-1]};
  };

  `uvm_object_utils_begin(tl_agent_cfg)
    `uvm_field_int(max_outstanding_req,   UVM_DEFAULT)
    `uvm_field_enum(tl_level_e, tl_level, UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_max,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_max,     UVM_DEFAULT)
    `uvm_field_queue_int(outstanding_req_fifo,  UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

endclass
