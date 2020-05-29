// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_base_vseq
  extends dv_base_vseq #(
    .CFG_T               (ibex_icache_env_cfg),
    .COV_T               (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T (ibex_icache_virtual_sequencer)
  );
  `uvm_object_utils(ibex_icache_base_vseq)
  `uvm_object_new

  // The two actual sequences. We don't subclass them in subclasses of this virtual sequence, but we
  // might want to set control knobs. To allow this, we construct the sequences in pre_start.
  // Subclasses should override pre_start, call this super to construct the sequence, and then set
  // any control knobs they need.
  ibex_icache_core_base_seq core_seq;
  ibex_icache_mem_resp_seq  mem_seq;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
  endtask

  virtual task pre_start();
    super.pre_start();
    `uvm_create_on(core_seq, p_sequencer.core_sequencer_h)
    `uvm_create_on(mem_seq, p_sequencer.mem_sequencer_h)
  endtask : pre_start

  virtual task body();
    // Start the core and memory sequences. We use fork/join_any so that we don't wait for the
    // memory sequence (which is reactive so will never finish).
    fork
      begin
        `DV_CHECK_RANDOMIZE_FATAL(core_seq)
        core_seq.start(p_sequencer.core_sequencer_h);
      end
      begin
        `DV_CHECK_RANDOMIZE_FATAL(mem_seq)
        mem_seq.start(p_sequencer.mem_sequencer_h);
      end
    join_any
  endtask : body

  virtual task dut_shutdown();
    // check for pending ibex_icache operations and wait for them to complete
    // TODO
  endtask

endclass : ibex_icache_base_vseq
