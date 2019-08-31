// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class irq_agent #(int src=32) extends uvm_agent;

  // To connect to scoreboard
  uvm_analysis_port #(irq_seq_item#(src)) m_irq_port;

  // No response required. So no irq_driver yet.
  irq_monitor #(src) m_mon;
  irq_sequencer #(src) m_seqr;

  `uvm_component_utils(irq_agent)

  function new (string name, uvm_component parent);
    super.new(name, parent);
    m_irq_port = new("m_irq_port", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Assume get_is_active() != UVM_ACTIVE
    //assert (get_is_active() != UVM_ACTIVE);

    m_seqr = irq_sequencer::type_id::create("m_seqr", this);
    m_mon = irq_monitor::type_id::create("m_mon", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    m_mon.m_irq_port.connect(m_seqr.m_irq_export);
    m_mon.m_irq_port.connect(m_irq_port);
  endfunction : connect_phase

endclass : irq_agent
