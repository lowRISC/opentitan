// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_driver extends dv_base_driver #(pattgen_item, pattgen_agent_cfg);
  `uvm_component_utils(pattgen_driver)
  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_ni);
      `uvm_info(`gfn, "\n  driver in reset progress", UVM_DEBUG)
      @(posedge cfg.vif.rst_ni);
      `uvm_info(`gfn, "\n  driver out of reset", UVM_DEBUG)
    end
  endtask : reset_signals

endclass : pattgen_driver
