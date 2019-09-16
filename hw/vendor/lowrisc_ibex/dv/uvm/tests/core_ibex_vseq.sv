// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Ibex core virtual sequence
// ---------------------------------------------

class core_ibex_vseq extends uvm_sequence;

  ibex_mem_intf_slave_seq                       instr_intf_seq;
  ibex_mem_intf_slave_seq                       data_intf_seq;
  mem_model_pkg::mem_model                      mem;
  irq_seq                                       irq_seq_stress_h;
  irq_seq                                       irq_seq_single_h;
  debug_seq                                     debug_seq_stress_h;
  debug_seq                                     debug_seq_single_h;
  core_ibex_env_cfg                             cfg;
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0]  data;

  `uvm_object_utils(core_ibex_vseq)
  `uvm_declare_p_sequencer(core_ibex_vseqr)
  `uvm_object_new

  virtual task body();
    instr_intf_seq = ibex_mem_intf_slave_seq::type_id::create("instr_intf_seq");
    data_intf_seq  = ibex_mem_intf_slave_seq::type_id::create("data_intf_seq");
    if (cfg.enable_irq_stress_seq) begin
      irq_seq_stress_h = irq_seq::type_id::create("irq_seq_stress_h");
      irq_seq_stress_h.max_interval = cfg.max_interval;
    end
    if (cfg.enable_irq_single_seq) begin
      irq_seq_single_h = irq_seq::type_id::create("irq_seq_single_h");
      irq_seq_single_h.num_of_iterations = 1;
      irq_seq_single_h.max_interval = 1;
      irq_seq_single_h.max_delay = 1;
      irq_seq_single_h.interval.rand_mode(0);
      irq_seq_single_h.interval = 0;
    end
    if (cfg.enable_debug_stress_seq) begin
      debug_seq_stress_h = debug_seq::type_id::create("debug_seq_stress_h");
      debug_seq_stress_h.max_interval = cfg.max_interval;
    end
    if (cfg.enable_debug_single_seq) begin
      debug_seq_single_h = debug_seq::type_id::create("debug_seq_single_h");
      debug_seq_single_h.num_of_iterations = 1;
      debug_seq_single_h.max_interval = 1;
      debug_seq_single_h.max_delay = 1;
      debug_seq_single_h.interval.rand_mode(0);
      debug_seq_single_h.interval = 0;
    end
    instr_intf_seq.m_mem = mem;
    data_intf_seq.m_mem  = mem;
    fork
      instr_intf_seq.start(p_sequencer.instr_if_seqr);
      data_intf_seq.start(p_sequencer.data_if_seqr);
    join_none
  endtask

  virtual task stop();
    if (cfg.enable_irq_stress_seq) begin
      irq_seq_stress_h.stop();
    end
    if (cfg.enable_irq_single_seq) begin
      irq_seq_single_h.stop();
    end
    if (cfg.enable_debug_stress_seq) begin
      debug_seq_stress_h.stop();
    end
    if (cfg.enable_debug_single_seq) begin
      debug_seq_single_h.stop();
    end
  endtask

  // Helper tasks to allow the test fine grained control to start sequences through the vseq
  // - necessary for testing directed stimulus scenarios
  virtual task start_debug_stress_seq();
    debug_seq_stress_h.start(null);
  endtask

  virtual task start_debug_single_seq();
    debug_seq_single_h.start(null);
  endtask

  virtual task start_irq_stress_seq();
    irq_seq_stress_h.start(p_sequencer.irq_seqr);
  endtask

  virtual task start_irq_single_seq();
    irq_seq_single_h.start(p_sequencer.irq_seqr);
  endtask

endclass
