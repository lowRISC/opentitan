// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base class for a driver. This drives sequence items of type ITEM_T. If the subclass is designed
// to do so, it responds with items of type RSP_ITEM_T.
//
// NOTE: This class would make more sense as an abstract base class (with a pure virtual
//       implementation of get_and_drive). Unfortunately, this isn't possible at the moment because
//       dv_base_agent ends up needing to instantiate a uvm_driver instance unless parameters are
//       overridden. This would be reasonable except that uvm_driver::create is not implemented in
//       UVM 1.2 (the version that OpenTitan currently depends on).
//
//       If we bump the UVM version past 1800.2-2020, we can switch this over to an abstract base
//       class.

class dv_base_driver #(type ITEM_T     = uvm_sequence_item,
                       type CFG_T      = dv_base_agent_cfg,
                       type RSP_ITEM_T = ITEM_T)
  extends uvm_driver #(.REQ(ITEM_T), .RSP(RSP_ITEM_T));

  `uvm_component_param_utils(dv_base_driver #(.ITEM_T     (ITEM_T),
                                              .CFG_T      (CFG_T),
                                              .RSP_ITEM_T (RSP_ITEM_T)))

  CFG_T cfg;

  extern function new (string name, uvm_component parent);

  // The run_phase task runs reset_signals() and get_and_drive() (described below) in parallel.
  // Subclasses might not need to implement run_phase directly.
  extern task run_phase(uvm_phase phase);

  // A task that runs forever, monitoring the cfg.in_reset flag and calling on_enter_reset when it
  // becomes true. Subclasses shouldn't normally need to override this.
  extern virtual task reset_signals();

  // The get_and_drive task should be implemented in any subclass. It must repeatedly call
  // get_next_item to consume items from the sequencer and, driving each.
  //
  // NOTE: Any implementation must implement this or fail at runtime. See note above for why this
  //       can't be enforced at build time.
  extern virtual task get_and_drive();

  // A task that is run at the start of any reset. It can be implemented by any subclass to clear
  // any driven signals back to their "reset value".
  //
  // Note that this task should not consume any simulation time: it is a task to allow it to
  // interact properly with clocking blocks.
  extern virtual task on_enter_reset();

  // A function that is run at the end of any reset. It may be implemented by any subclass and gives
  // the class an opportunity to set up values before the start of a run, but without a race
  // condition at the start of the reset.
  extern virtual function void on_leave_reset();
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
  forever begin
    `uvm_info(get_full_name(), "Driver entering reset", UVM_HIGH)
    on_enter_reset();
    wait(!cfg.in_reset);
    `uvm_info(get_full_name(), "Driver leaving reset", UVM_HIGH)
    on_leave_reset();
    wait(cfg.in_reset);
  end
endtask

task dv_base_driver::get_and_drive();
  `uvm_fatal(get_full_name(), "This task must be implemented by base classes.")
endtask

task dv_base_driver::on_enter_reset();
  // The default behaviour of this function is to do nothing
endtask

function void dv_base_driver::on_leave_reset();
  // The default behaviour of this function is to do nothing
endfunction
