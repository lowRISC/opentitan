// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_device_driver extends i2c_driver;
  `uvm_component_utils(i2c_device_driver)

  // the base class provides the following handles for use:
  // i2c_agent_cfg: cfg

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
  endtask

endclass
