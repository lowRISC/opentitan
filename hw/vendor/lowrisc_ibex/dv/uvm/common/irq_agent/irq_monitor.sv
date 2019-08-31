// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class irq_monitor extends uvm_monitor;

  protected virtual irq_if vif;

  uvm_analysis_port#(irq_seq_item) irq_port;

  `uvm_component_utils(irq_monitor)

  function new(string name, uvm_component parent=null);
    super.new(name, parent);
    irq_port = new("irq_port", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual irq_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
    end
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    collect_irq();
  endtask : run_phase

  virtual protected task collect_irq();
    irq_seq_item irq;
    forever begin
      if (|{vif.irq_software, vif.irq_timer, vif.irq_external,
            vif.irq_fast, vif.irq_nm}) begin
        irq = irq_seq_item::type_id::create("irq");
        irq.irq_software = vif.irq_software;
        irq.irq_timer = vif.irq_timer;
        irq.irq_external = vif.irq_external;
        irq.irq_fast = vif.irq_fast;
        irq.irq_nm = vif.irq_nm;
        irq_port.write(irq);
      end
      @(posedge vif.clock);
    end
  endtask : collect_irq

endclass : irq_monitor
