// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_host_driver extends i2c_driver;
  `uvm_component_utils(i2c_host_driver)
    `uvm_component_new


  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    fork
      super.run_phase(phase);
    join
  endtask : run_phase

  // reset signals
  virtual task reset_signals();
  endtask : reset_signals

  // drive trans received from sequencer
  virtual task get_and_drive();
  endtask : get_and_drive

endclass : i2c_host_driver
