// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_agent_cfg extends uvm_object;

  // agent cfg knobs
  bit         is_active = 1'b1;   // active driver/sequencer or passive monitor
  bit         en_cov    = 1'b1;   // enable coverage
  if_mode_e   if_mode;            // interface mode - Host or Device

  // indicate to create and connet driver to sequencer or not
  // if this is a high-level agent, we may just call lower-level agent to send item in seq, then
  // driver isn't needed
  bit         has_driver = 1'b1;
  // indicate if these fifo and ports exist or not
  bit         has_req_fifo = 1'b0;
  bit         has_rsp_fifo = 1'b0;

  // use for phase_ready_to_end to add additional delay after ok_to_end is set
  int ok_to_end_delay_ns = 1000;

  // Indicates that the interface is under reset. The derived monitor detects and maintains it.
  bit in_reset;

  `uvm_object_utils_begin(dv_base_agent_cfg)
    `uvm_field_int (is_active,            UVM_DEFAULT)
    `uvm_field_int (en_cov,               UVM_DEFAULT)
    `uvm_field_enum(if_mode_e, if_mode,   UVM_DEFAULT)
    `uvm_field_int (has_req_fifo,         UVM_DEFAULT)
    `uvm_field_int (has_rsp_fifo,         UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
