// Copyright lowRISC contributors (OpenTitan project).
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

  // Indicates that the interface is under reset. The monitor detects and maintains it as this
  // component is always created.
  // TODO MVy: that's probably not a good approach to share information via  the config class.
  // So this should be renamed into under_reset to be more coherent or this should be removed and
  // managed locally by each component (monitor, driver and sequencer).
  bit in_reset;

  // Control knob to set whether the agent requires reset handling. This will imply this agent
  // to react to reset state changes passed via the dedicated analysis port.
  // Note that most of the agents will require to implement this given that sequencer, driver and
  // monitor should drop any ongoing operation when a reset on-the-fly is occuring.
  bit has_reset = 1;

  bit en_monitor = 1'b1;

  `uvm_object_utils_begin(dv_base_agent_cfg)
    `uvm_field_int (is_active,            UVM_DEFAULT)
    `uvm_field_int (en_cov,               UVM_DEFAULT)
    `uvm_field_int (en_monitor,           UVM_DEFAULT)
    `uvm_field_int (has_driver,           UVM_DEFAULT)
    `uvm_field_int (in_reset,             UVM_DEFAULT)
    `uvm_field_int (has_reset,            UVM_DEFAULT)
    `uvm_field_enum(if_mode_e, if_mode,   UVM_DEFAULT)
    `uvm_field_int (has_req_fifo,         UVM_DEFAULT)
    `uvm_field_int (has_rsp_fifo,         UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
