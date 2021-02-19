// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_host_driver extends keymgr_kmac_driver;
  `uvm_component_utils(keymgr_kmac_host_driver)
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
