// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  // the base class provides the following handles for use:
  i2c_agent_cfg cfg;

  uvm_reg  csrs[$];

  bit      under_reset;
  bit      is_start;

  event    is_start_e;
  event    is_stop_e;

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    fork
      reset_signals();
      get_and_drive();
    join
  endtask

  virtual task reset_signals();
    wait(cfg.vif.rst_ni === 1'b0);
    cfg.vif.scl_o = 1'bx;
    cfg.vif.sda_o = 1'bx;
    under_reset   = 1'b1;
    is_start      = 1'bx;

    wait(cfg.vif.rst_ni === 1'b1);
    cfg.vif.scl_o = 1'b1;
    cfg.vif.sda_o = 1'b1;
    under_reset   = 1'b0;
    is_start      = 1'b0;
  endtask : reset_signals

  virtual task get_and_drive();
    //`uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

endclass : i2c_driver
