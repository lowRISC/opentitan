// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Ibex core virtual sequence
// ---------------------------------------------

class core_ibex_vseq extends uvm_sequence;

  ibex_mem_intf_response_seq                    instr_intf_seq;
  ibex_mem_intf_response_seq                    data_intf_seq;
  mem_model_pkg::mem_model                      mem;
  irq_raise_seq                                 irq_raise_seq_h;
  irq_raise_single_seq                          irq_raise_single_seq_h;
  irq_raise_nmi_seq                             irq_raise_nmi_seq_h;
  irq_drop_seq                                  irq_drop_seq_h;
  debug_seq                                     debug_seq_stress_h;
  debug_seq                                     debug_seq_single_h;
  fetch_enable_seq                              fetch_enable_seq_h;
  core_ibex_env_cfg                             cfg;
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0]  data;

  `uvm_object_utils(core_ibex_vseq)
  `uvm_declare_p_sequencer(core_ibex_vseqr)

  function new (string name = "");
    super.new(name);
    instr_intf_seq = ibex_mem_intf_response_seq::type_id::create("instr_intf_seq");
    data_intf_seq  = ibex_mem_intf_response_seq::type_id::create("data_intf_seq");
    data_intf_seq.is_dmem_seq = 1'b1;
  endfunction

  // Start the memory-model sequences, which run forever() loops to respond to bus events
  virtual task pre_body();
    instr_intf_seq.m_mem = mem;
    data_intf_seq.m_mem  = mem;
    fork
      instr_intf_seq.start(p_sequencer.instr_if_seqr);
      data_intf_seq.start(p_sequencer.data_if_seqr);

      if (!cfg.disable_fetch_enable_seq) begin
        fetch_enable_seq_h = fetch_enable_seq::type_id::create("fetch_enable_seq_h");
        fetch_enable_seq_h.iteration_modes = InfiniteRuns;
        fetch_enable_seq_h.stimulus_delay_cycles_min = 1000;
        fetch_enable_seq_h.stimulus_delay_cycles_max = 2000;

        fetch_enable_seq_h.start(null);
      end
    join_none
  endtask // pre_body

  virtual task body();
    if (cfg.enable_irq_single_seq) begin
      irq_raise_single_seq_h = irq_raise_single_seq::type_id::create("irq_single_seq_h");
      irq_raise_single_seq_h.num_of_iterations = 1;
      irq_raise_single_seq_h.max_interval = 1;
      irq_raise_single_seq_h.max_delay = 500;
      irq_raise_single_seq_h.interval = 0;
    end
    if (cfg.enable_irq_multiple_seq) begin
      irq_raise_seq_h = irq_raise_seq::type_id::create("irq_raise_seq_h");
      irq_raise_seq_h.num_of_iterations = 1;
      irq_raise_seq_h.max_interval = 1;
      irq_raise_seq_h.max_delay = 500;
      irq_raise_seq_h.interval = 0;
    end
    if (cfg.enable_irq_nmi_seq) begin
      irq_raise_nmi_seq_h = irq_raise_nmi_seq::type_id::create("irq_raise_nmi_seq_h");
      irq_raise_nmi_seq_h.num_of_iterations = 1;
      irq_raise_nmi_seq_h.max_interval = 1;
      irq_raise_nmi_seq_h.max_delay = 500;
      irq_raise_nmi_seq_h.interval = 0;
    end
    if (cfg.enable_irq_single_seq || cfg.enable_irq_multiple_seq || cfg.enable_irq_nmi_seq) begin
      irq_drop_seq_h = irq_drop_seq::type_id::create("irq_drop_seq_h");
      irq_drop_seq_h.num_of_iterations = 1;
      irq_drop_seq_h.max_interval = 1;
      irq_drop_seq_h.max_delay = 0;
      irq_drop_seq_h.interval = 0;
    end
    if (cfg.enable_debug_seq) begin
      debug_seq_stress_h = debug_seq::type_id::create("debug_seq_stress_h");
      debug_seq_stress_h.max_interval = cfg.max_interval;

      debug_seq_single_h = debug_seq::type_id::create("debug_seq_single_h");
      debug_seq_single_h.num_of_iterations = 1;
      debug_seq_single_h.max_interval = 1;
      debug_seq_single_h.max_delay = 1;
      debug_seq_single_h.interval.rand_mode(0);
      debug_seq_single_h.interval = 0;
    end
  endtask

  virtual task stop();
    if (cfg.enable_irq_single_seq) begin
      if (irq_raise_single_seq_h.is_started) irq_raise_single_seq_h.stop();
    end
    if (cfg.enable_irq_multiple_seq) begin
      if (irq_raise_seq_h.is_started) irq_raise_seq_h.stop();
    end
    if (cfg.enable_irq_single_seq || cfg.enable_irq_multiple_seq) begin
      if (irq_drop_seq_h.is_started)   irq_drop_seq_h.stop();
    end
    if (cfg.enable_debug_seq) begin
      if (debug_seq_stress_h.is_started) debug_seq_stress_h.stop();
      if (debug_seq_single_h.is_started) debug_seq_single_h.stop();
    end
  endtask

  virtual task wait_for_stop();
    if (cfg.enable_irq_single_seq) begin
      if (irq_raise_single_seq_h.is_started) irq_raise_single_seq_h.wait_for_stop();
    end
    if (cfg.enable_irq_multiple_seq) begin
      if (irq_raise_seq_h.is_started) irq_raise_seq_h.wait_for_stop();
    end
    if (cfg.enable_irq_single_seq || cfg.enable_irq_multiple_seq) begin
      if (irq_drop_seq_h.is_started)   irq_drop_seq_h.wait_for_stop();
    end
    if (cfg.enable_debug_seq) begin
      if (debug_seq_stress_h.is_started) debug_seq_stress_h.wait_for_stop();
      if (debug_seq_single_h.is_started) debug_seq_single_h.wait_for_stop();
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

  virtual task start_irq_raise_single_seq(bit no_nmi = 1'b0, bit no_fast = 1'b0);
    irq_raise_single_seq_h.no_nmi = no_nmi;
    irq_raise_single_seq_h.no_fast = no_fast;
    irq_raise_single_seq_h.start(p_sequencer.irq_seqr);
  endtask

  virtual task start_irq_raise_seq(bit no_nmi = 1'b0, bit no_fast = 1'b0);
    irq_raise_seq_h.no_nmi = no_nmi;
    irq_raise_seq_h.no_fast = no_fast;
    irq_raise_seq_h.start(p_sequencer.irq_seqr);
  endtask

  virtual task start_nmi_raise_seq();
    irq_raise_nmi_seq_h.start(p_sequencer.irq_seqr);
  endtask

  virtual task start_irq_drop_seq();
    irq_drop_seq_h.start(p_sequencer.irq_seqr);
  endtask


endclass
