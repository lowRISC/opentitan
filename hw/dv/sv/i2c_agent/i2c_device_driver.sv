// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __I2C_DRIVE_DRIVER__
`define __I2C_DRIVE_DRIVER__

class i2c_drive_driver extends i2c_driver;
  `uvm_component_utils(i2c_drive_driver)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ( cfg  == null )
      `uvm_fatal(`gtn, "failed due to null i2c_cfg")
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    reset_signals;
    get_and_drive();
  endtask : run_phase

  // resets signals.
  virtual task reset_signals();
    super.reset_signals();
  endtask : reset_signals

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_LOW)
      // TODO: do the driving part

      // send rsp back to seq
      `uvm_info(`gfn, "item sent", UVM_LOW)
      seq_item_port.item_done(rsp);
    end
  endtask : get_and_drive

  // wait for start
  task wait_for_start (uvm_phase phase);
    mon_start(is_start_e);
    if (is_start_e.triggered) begin
      `uvm_info(`gtn, "detected start event, raise object", UVM_LOW)
      is_start = 1'b1;
      phase.raise_objection(this);
    end
  endtask: wait_for_start

  // wait for stop
  task wait_for_stop (uvm_phase phase);
    mon_stop(is_stop_e);
    if (is_stop_e.triggered) begin
      `uvm_info(`gtn, "detected stop event", UVM_LOW)
      if (is_start) begin
        `uvm_info(`gtn, "start event issued before, drop object", UVM_LOW)
        is_start = 1'b0;
        phase.drop_objection(this);
      end
    end
  endtask: wait_for_stop

  // monitor start condition
  task mon_start( ref event start_e );
    wait(cfg.vif.drv_cb.sda_i !== 1'bx);
    @(negedge cfg.vif.drv_cb.sda_i);
    if (cfg.vif.drv_cb.scl_i === 1'b1) begin
      ->start_e;
      cfg.i2c_bus_status = START;
    end
  endtask: mon_start

  // monitor stop condition
  task mon_stop( ref event stop_e );
    wait(cfg.vif.drv_cb.sda_i !== 1'bx);
    @(posedge cfg.vif.drv_cb.sda_i);
    if (cfg.vif.drv_cb.scl_i === 1'b1) begin
      ->stop_e;
      cfg.i2c_bus_status = STOP;
    end
  endtask: mon_stop

endclass : i2c_drive_driver

`endif // __I2C_DRIVE_DRIVER__