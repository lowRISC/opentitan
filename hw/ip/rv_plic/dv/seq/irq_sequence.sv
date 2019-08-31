// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class irq_sequence #(int src = 32) extends uvm_sequence#(irq_seq_item);

  `uvm_declare_p_sequencer(irq_sequencer)

  `uvm_object_utils(irq_sequence)

  irq_seq_item #(src) m_irq;

  function new(string name="irq_sequence");
    super.new(name);
    m_irq = new();
  endfunction : new

  virtual task body();
    forever begin
      p_sequencer.m_irq_fifo.get(m_irq);
      m_irq.print();

      // Trigger tl_agent for interrupt handling
      // Claim
      //
      // Delay
      //
      // Complete
    end
  endtask : body

endclass : irq_sequence
