// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __I2C_COMMON_TASKS__
`define __I2C_COMMON_TASKS__

class i2c_common_tasks extends uvm_object;
  `uvm_object_utils(i2c_common_tasks)

  virtual i2c_if vif;

  function new(string name = "i2c_common_tasks");
    super.new(name);
  endfunction: new

  // wait for random delay
  task wait_for_rand_dly(int dly);
    repeat (dly) @(posedge vif.clk_i);
  endtask : wait_for_rand_dly

  // send ack by device to acknowledge address/write data byte
  task send_ack_by_device();
    vif.scl_o <= 1'b1;
    vif.sda_o <= 1'b0;
  endtask: send_ack_by_device

  task wait_for_bus_free();
    @(vif.scl_i === 1'b1 && vif.sda_i === 1'b1)
    #4.7us vif.status = "FREE";
  endtask : wait_for_bus_free

  // detect start condition sent by host
  task wait_for_ack_by_dev();
    wait(vif.scl_o === 1'b0 && vif.sda_o === 1'b0 );
    @(negedge vif.scl_o);
    vif.status = "DEV_ACK";
  endtask: wait_for_ack_by_dev

  // detect start condition sent by host
  task wait_for_start_by_host();
    wait(vif.drv_rx_cb.sda_i !== 1'bx);
    @(negedge vif.drv_rx_cb.sda_i);
    vif.status = "START";
  endtask: wait_for_start_by_host

  // detect repeated start condition sent by host
  task wait_for_repstart_by_host();
    wait(vif.scl_i !== 1'bx);
    @(posedge vif.scl_i);
    vif.status = "REP_START";
  endtask: wait_for_repstart_by_host

  // detect stop condition sent by host
  task wait_for_stop_by_host ();
    wait(vif.sda_i !== 1'bx);
    @(posedge vif.sda_i);
    vif.status = "STOP";
  endtask: wait_for_stop_by_host

  // detect nack condition sent by host
  task wait_for_ack_by_host();
    wait(vif.scl_i === 1'b0 && vif.sda_i === 1'b0 );
    @(posedge vif.scl_i);
    vif.status = "HST_ACK";
  endtask: wait_for_ack_by_host

  // detect nack condition sent by host
  task wait_for_nack_by_host(output bit nack);
    wait(vif.scl_i === 1'b0 && vif.sda_i === 1'b1 );
    @(posedge vif.scl_i);
    nack = vif.sda_i;    // 1: nack, 0: ack
    vif.status = "HST_NACK";
  endtask: wait_for_nack_by_host
  
endclass : i2c_common_tasks

`endif  // __I2C_COMMON_TASKS__