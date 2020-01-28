// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  // the base class provides the following handles for use:
  i2c_agent_cfg       cfg;
  i2c_item            dev_item;
  i2c_common_tasks    common_tasks;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    dev_item = i2c_item::type_id::create("dev_item");
    if (dev_item === null)
      `uvm_fatal(`gtn, "failed due to null dev_item")

    common_tasks = i2c_common_tasks::type_id::create("common_tasks", this);
    common_tasks.vif = cfg.vif;
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    reset_signals();
  endtask : run_phase

  virtual task reset_signals();
    `uvm_info(`gtn, "driver in reset progress", UVM_LOW)
    wait(cfg.vif.rst_ni === 1'b0);
    cfg.vif.scl_o <= 1'bx;
    cfg.vif.sda_o <= 1'bx;

    wait(cfg.vif.rst_ni === 1'b1);
    `uvm_info(`gtn, "driver out of reset", UVM_LOW)
    cfg.vif.scl_o <= 1'b1;
    cfg.vif.sda_o <= 1'b1;
  endtask : reset_signals
endclass : i2c_driver
