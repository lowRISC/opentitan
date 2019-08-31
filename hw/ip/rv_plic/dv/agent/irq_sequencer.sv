// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class irq_sequencer #(int src = 32) extends uvm_sequencer #(irq_seq_item);

  `uvm_sequencer_utils(irq_sequencer)

  uvm_analysis_export #(irq_seq_item#(src)) m_irq_export;
  uvm_tlm_analysis_fifo #(irq_seq_item#(src)) m_irq_fifo;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    m_irq_fifo = new("m_irq_fifo", this);
    m_irq_export = new("m_irq_export", this);
  endfunction : new

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    m_irq_export.connect(m_irq_fifo.analysis_export);
  endfunction : connect_phase

endclass : irq_sequencer
