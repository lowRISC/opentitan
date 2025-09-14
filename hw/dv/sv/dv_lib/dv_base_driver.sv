// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base class for a driver of an agent. This drives sequence items of type ITEM_T. If the subclass
// is designed to do so, it responds with items of type RSP_ITEM_T.

class dv_base_driver #(type ITEM_T     = uvm_sequence_item,
                       type CFG_T      = dv_base_agent_cfg,
                       type RSP_ITEM_T = ITEM_T)
  extends uvm_driver #(.REQ(ITEM_T), .RSP(RSP_ITEM_T));

  `uvm_component_param_utils(dv_base_driver #(.ITEM_T     (ITEM_T),
                                              .CFG_T      (CFG_T),
                                              .RSP_ITEM_T (RSP_ITEM_T)))

  bit   under_reset;
  CFG_T cfg;

  extern function new (string name, uvm_component parent);

  // The run_phase task runs reset_signals() and get_and_drive() (described below) in parallel.
  // Subclasses might not need to implement run_phase directly.
  extern task run_phase(uvm_phase phase);

  // The reset_signals task should be implemented in any subclass and is responsible for monitoring
  // reset on the interface, then resetting the driven signals when a reset happens.
  extern virtual task reset_signals();

  // The get_and_drive task should be implemented in any subclass. It must repeatedly call
  // get_next_item to consume items from the sequencer and, driving each.
  extern virtual task get_and_drive();
endclass

function dv_base_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task dv_base_driver::run_phase(uvm_phase phase);
  super.run_phase(phase);
  fork
    reset_signals();
    get_and_drive();
  join
endtask

task dv_base_driver::reset_signals();
  // Empty - to be populated in child class
endtask

task dv_base_driver::get_and_drive();
  // Empty - to be populated in child class
endtask
