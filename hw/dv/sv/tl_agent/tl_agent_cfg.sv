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

  // If allow_a_valid_drop_wo_a_ready then the host can de-assert valid if there is no response from
  // the device on the A channel. The other knobs control how this works. Each transaction has a
  // "valid_len". If the host hasn't seen a ready after holding valid high for that many cycles, it
  // will de-assert valid for a time before retrying.
  //
  // If use_seq_item_a_valid_len is true then valid_len will be read from the sequence item (field
  // a_valid_len). If not, it will be picked uniformly between a_valid_len_min and a_valid_len_max.
  bit allow_a_valid_drop_wo_a_ready = 1;
  bit use_seq_item_a_valid_len;
  int unsigned a_valid_len_min = 1;
  int unsigned a_valid_len_max = 10;

  // Knobs controlling when we de-assert valid in device mode: see above for the host mode
  // equivalent.
  bit use_seq_item_d_valid_len;
  bit allow_d_valid_drop_wo_d_ready;
  int unsigned d_valid_len_min = 1;
  int unsigned d_valid_len_max = 10;

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

  // TL spec requires host to set d_ready = 1 when a_valid = 1, but some design may not follow this
  // rule. Details at #3208. Use below knob to control
  bit host_can_stall_rsp_when_a_valid_high = 0;
  // knob for device to enable/disable same cycle response
  bit device_can_rsp_on_same_cycle = 0;
  // for same cycle response, need to know when a_valid and other data/control are available, so
  // that monitor can sample it, then send to sequence to get data for response in the same cycle
  // 10 means 10% of TL clock period. This var is only use when device_can_rsp_on_same_cycle = 1
  time time_a_valid_avail_after_sample_edge = 1ns;

  `uvm_object_utils_begin(tl_agent_cfg)
    `uvm_field_int(max_outstanding_req,   UVM_DEFAULT)
    `uvm_field_enum(tl_level_e, tl_level, UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_max,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_max,     UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

endclass
