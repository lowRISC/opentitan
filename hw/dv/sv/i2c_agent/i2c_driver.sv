// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    reset_signals();
  endtask : run_phase

  virtual task reset_signals();
    `uvm_info(`gtn, "driver in reset progress", UVM_DEBUG)
    wait(cfg.vif.rst_ni === 1'b0);
    cfg.vif.scl_o <= 1'bx;
    cfg.vif.sda_o <= 1'bx;
    @(cfg.vif.drv_tx_mp.drv_tx_cb);

    wait(cfg.vif.rst_ni === 1'b1);
    `uvm_info(`gtn, "driver out of reset", UVM_DEBUG)
    cfg.vif.scl_o <= 1'b1;
    cfg.vif.sda_o <= 1'b1;
    cfg.vif.bus_status = BusFree;
    @(cfg.vif.drv_tx_mp.drv_tx_cb);

  endtask : reset_signals

endclass : i2c_driver
