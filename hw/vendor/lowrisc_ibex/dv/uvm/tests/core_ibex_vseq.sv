// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Ibex core virtual sequence
// ---------------------------------------------

class core_ibex_vseq extends uvm_sequence;

  ibex_mem_intf_slave_seq    instr_intf_seq;
  ibex_mem_intf_slave_seq    data_intf_seq;
  mem_model_pkg::mem_model   mem;
  irq_seq                    irq_seq_h;
  debug_seq                  debug_seq_h;
  core_ibex_env_cfg          cfg;

  `uvm_object_utils(core_ibex_vseq)
  `uvm_declare_p_sequencer(core_ibex_vseqr)
  `uvm_object_new

  virtual task body();
    instr_intf_seq = ibex_mem_intf_slave_seq::type_id::create("instr_intf_seq");
    data_intf_seq  = ibex_mem_intf_slave_seq::type_id::create("data_intf_seq");
    instr_intf_seq.m_mem = mem;
    data_intf_seq.m_mem  = mem;

    fork
      instr_intf_seq.start(p_sequencer.instr_if_seqr);
      data_intf_seq.start(p_sequencer.data_if_seqr);
      if (cfg.enable_irq_seq) begin
        irq_seq_h = irq_seq::type_id::create("irq_seq_h");
        irq_seq_h.start(p_sequencer.irq_seqr);
      end
      if (cfg.enable_debug_seq) begin
        debug_seq_h = debug_seq::type_id::create("debug_seq_h");
        debug_seq_h.start(null);
      end
    join_none
  endtask

  virtual task stop();
    if (cfg.enable_irq_seq) begin
      irq_seq_h.stop();
    end
    if (cfg.enable_debug_seq) begin
      debug_seq_h.stop();
    end
  endtask

endclass
