// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  virtual task reset_signals();
    `uvm_info(`gfn, "driver in reset progress", UVM_HIGH)
    @(negedge cfg.vif.rst_ni);
    cfg.vif.scl_o <= 1'b0;
    cfg.vif.sda_o <= 1'b0;
    @(posedge cfg.vif.rst_ni);
    cfg.vif.scl_o <= 1'b1;
    cfg.vif.sda_o <= 1'b1;
    `uvm_info(`gfn, "driver out of reset", UVM_HIGH)
  endtask : reset_signals

endclass : i2c_driver
