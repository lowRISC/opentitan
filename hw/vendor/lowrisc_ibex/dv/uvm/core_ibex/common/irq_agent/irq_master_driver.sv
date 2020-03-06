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
    reset_signals();
    forever begin
      fork : drive_irq
        get_and_drive();
        wait(vif.reset === 1'b1);
      join_any
      // Will only reach here on mid-test reset
      disable drive_irq;
      handle_reset();
    end
  endtask : run_phase

  virtual protected task handle_reset();
    irq_seq_item req;
    // Clear seq_item_port
    do begin
      seq_item_port.try_next_item(req);
      if (req != null) begin
        seq_item_port.item_done();
      end
    end while (req != null);
    reset_signals();
  endtask

  virtual protected task get_and_drive();
    wait(vif.reset === 1'b0);
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
    @(negedge vif.reset);
    drive_reset_value();
  endtask : reset_signals

  virtual protected task drive_seq_item (irq_seq_item trans);
    vif.irq_software <= trans.irq_software;
    vif.irq_timer    <= trans.irq_timer;
    vif.irq_external <= trans.irq_external;
    vif.irq_fast     <= trans.irq_fast;
    vif.irq_nm       <= trans.irq_nm;
  endtask : drive_seq_item

  task drive_reset_value();
    vif.irq_software <= '0;
    vif.irq_timer    <= '0;
    vif.irq_external <= '0;
    vif.irq_fast     <= '0;
    vif.irq_nm       <= '0;
  endtask : drive_reset_value

endclass : irq_master_driver

