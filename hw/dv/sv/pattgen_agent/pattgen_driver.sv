// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_driver extends dv_base_driver #(pattgen_item, pattgen_agent_cfg);
  `uvm_component_utils(pattgen_driver)
  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_ni);
      `uvm_info(`gfn, "\ndriver in reset progress", UVM_DEBUG)
      @(posedge cfg.vif.rst_ni);
      `uvm_info(`gfn, "\ndriver out of reset", UVM_DEBUG)
    end
  endtask : reset_signals

  virtual task get_and_drive();
    @(posedge cfg.vif.rst_ni);
    // pattgen does not require responses from pattgen_agent thus this task is kept to a minimum
  endtask : get_and_drive

endclass : pattgen_driver
