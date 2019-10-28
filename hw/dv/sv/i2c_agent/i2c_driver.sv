// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_driver extends dv_base_driver #(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_driver)

  `uvm_component_new

  // the base class provides the following handles for use:
  i2c_agent_cfg  cfg;
  //i2c_item       device_item;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    fork
      reset_signals();
      get_and_drive();
    join
  endtask

  virtual task reset_signals();
    wait(cfg.vif.rst_ni === 1'b0);
    cfg.vif.drv_cb.scl_o <= 1'bx;
    cfg.vif.drv_cb.sda_o <= 1'bx;
    cfg.i2c_bus_status <= RESET;

    wait(cfg.vif.rst_ni === 1'b1);
    @(posedge cfg.vif.drv_cb.scl_i === 1'b1);
    if (cfg.vif.drv_cb.scl_i === 1'b1) begin
      cfg.vif.drv_cb.scl_o <= 1'b1;
      cfg.vif.drv_cb.sda_o <= 1'b1;
      cfg.i2c_bus_status <= FREE;
    end
  endtask : reset_signals

  virtual task get_and_drive();

  endtask : get_and_drive

  // wait for random delay
  task wait_for_rand_dly (int dly);
    repeat (dly) @(posedge cfg.vif.clk_i);
  endtask : wait_for_rand_dly

  // send ack by device to acknowledge address/write data byte
  task send_ack_by_device ();
    cfg.vif.drv_cb.scl_o <= 1'b1;
    cfg.vif.drv_cb.sda_o <= 1'b0;
  endtask: send_ack_by_device

  // detect start condition sent by host
  task wait_for_start_by_host ();
    wait(cfg.vif.drv_cb.sda_i !== 1'bx);
    @(negedge cfg.vif.drv_cb.sda_i)
    if (cfg.vif.drv_cb.scl_i === 1'b1)
      cfg.i2c_bus_status <= START;
  endtask: wait_for_start_by_host

  // detect repeated start condition sent by host
  task wait_for_repeated_start_by_host ();
    wait(cfg.vif.drv_cb.scl_i !== 1'bx);
    @(posedge cfg.vif.drv_cb.scl_i)
    if (cfg.vif.drv_cb.sda_i === 1'b1)
      cfg.i2c_bus_status <= REPSTART;
  endtask: wait_for_repeated_start_by_host

  // detect stop condition sent by host
  task wait_for_stop_by_host ();
    wait(cfg.vif.drv_cb.sda_i !== 1'bx);
    @(posedge cfg.vif.drv_cb.sda_i)
    if (cfg.vif.drv_cb.scl_i === 1'b1)
      cfg.i2c_bus_status <= STOP;
  endtask: wait_for_stop_by_host

  // detect nack condition sent by host
  task wait_for_ack_by_host ();
    wait(cfg.vif.drv_cb.scl_i === 1'b0 && cfg.vif.drv_cb.sda_i === 1'b0 );
    @(posedge cfg.vif.drv_cb.scl_i)
    if (cfg.vif.drv_cb.sda_i === 1'b0)
      cfg.i2c_bus_status <= ACK;
  endtask: wait_for_ack_by_host

  // detect nack condition sent by host
  task wait_for_nack_by_host ();
    wait(cfg.vif.drv_cb.scl_i === 1'b0 && cfg.vif.drv_cb.sda_i === 1'b1 );
    @(posedge cfg.vif.drv_cb.scl_i)
    if (cfg.vif.drv_cb.sda_i === 1'b1)
      cfg.i2c_bus_status <= NACK;
  endtask: wait_for_nack_by_host

endclass : i2c_driver
