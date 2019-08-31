// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class irq_monitor #(int src=32) extends uvm_monitor;

  virtual plic_if #(src) vif;

  //uvm_analysis_port #(transaction) m_bus_port; // for scoreboard
  uvm_analysis_port #(irq_seq_item#(src)) m_irq_port;

  irq_seq_item #(src) trans_collected;

  `uvm_component_utils(irq_monitor)

  function new(string name, uvm_component parent);
    super.new(name, parent);
    m_irq_port = new("m_irq_port", this);
    trans_collected = new();
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual plic_if)::get(this,"","pif",vif)) begin
      `uvm_fatal("NO_VIF", {"virtual interface must be set for:",
        get_full_name(),".vif"});
    end
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    trans_collected.irq_id = '0; // No Interrupt

    forever begin
      // Add IRQ catch and generate
      // ...
      @(posedge vif.clk iff (vif.irq == 1'b1 && vif.irq_id != '0));
      if (trans_collected.irq_id != vif.irq_id) begin
        // New transaction occurred. Report to sequencer
        trans_collected = new();
        trans_collected.irq_id = vif.irq_id;

        // Write sequence to Analysis Port so that sequencer can its job
        m_irq_port.write(trans_collected);
        //m_bus_port.write(trans_collected);
      end
    end
  endtask : run_phase

endclass : irq_monitor
