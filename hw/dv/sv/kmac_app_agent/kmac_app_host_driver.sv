// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_host_driver extends kmac_app_driver;
  `uvm_component_utils(kmac_app_host_driver)
  `uvm_component_new


  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  virtual task reset_signals();
  endtask

  virtual task get_and_drive();
  endtask

endclass
