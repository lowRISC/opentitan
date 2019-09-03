// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class irq_master_driver extends uvm_driver #(irq_seq_item);

  // The virtual interface used to drive and view HDL signals.
  protected virtual irq_if vif;

  `uvm_component_utils(irq_master_driver)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual irq_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
    end
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
    join
  endtask : run_phase

  virtual protected task get_and_drive();
    @(negedge vif.reset);
    forever begin
      seq_item_port.try_next_item(req);
      if (req != null) begin
        $cast(rsp, req.clone());
        rsp.set_id_info(req);
        drive_seq_item(rsp);
        seq_item_port.item_done(rsp);
      end else begin
        @(posedge vif.clock);
      end
    end
  endtask : get_and_drive

  virtual protected task reset_signals();
    forever begin
      @(posedge vif.reset);
      drive_reset_value();
    end
  endtask : reset_signals

  virtual protected task drive_seq_item (irq_seq_item trans);
    vif.irq_software <= trans.irq_software;
    vif.irq_timer    <= trans.irq_timer;
    vif.irq_external <= trans.irq_external;
    vif.irq_fast     <= trans.irq_fast;
    vif.irq_nm       <= trans.irq_nm;
    // We hold the interrupt high for two cycles as Ibex is level sensitive,
    // so this guarantees that Ibex will respond appropriately to the
    // interrupt
    repeat (2) @(posedge vif.clock);
    drive_reset_value();
  endtask : drive_seq_item

  task drive_reset_value();
    vif.irq_software <= '0;
    vif.irq_timer    <= '0;
    vif.irq_external <= '0;
    vif.irq_fast     <= '0;
    vif.irq_nm       <= '0;
  endtask : drive_reset_value

endclass : irq_master_driver

