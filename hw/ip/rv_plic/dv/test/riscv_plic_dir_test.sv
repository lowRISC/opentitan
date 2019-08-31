// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class riscv_plic_dir_test extends uvm_test;

  `uvm_component_utils(riscv_plic_dir_test)

  plic_env                      env;
  plic_dir_sequence #(.src(32)) seq;
  irq_sequence      #(.src(32)) irq_seq;

  function new(string name ="riscv_plic_dir_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    env = plic_env::type_id::create("env", this);
    seq = plic_dir_sequence::type_id::create("seq");
    irq_seq = irq_sequence::type_id::create("irq_seq");
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    env.m_irqagt.m_irq_port.connect(seq.m_irq_fifo.analysis_export);
  endfunction : connect_phase

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    fork
      irq_seq.start(env.m_irqagt.m_seqr);
    join_none
    seq.start(env.m_tlagt.m_seqr);
    phase.drop_objection(this);
  endtask : run_phase

endclass : riscv_plic_dir_test
