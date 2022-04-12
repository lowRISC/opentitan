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

  // The mem_err_shift parameter to use for the memory model with this sequence. Gets written to the
  // sequencer's config when the sequence runs.
  int unsigned mem_err_shift = 3;

  // Non-null if this is an item after the first in a "combo" run, which runs several of these
  // sequences back-to-back. Must be set before pre_start to have any effect.
  ibex_icache_base_vseq prev_sequence = null;

  // The core and memory sequences. We don't subclass them in subclasses of this virtual sequence,
  // but we might want to set control knobs. To allow this, we construct the sequences in pre_start.
  // Subclasses should override pre_start, call this super to construct the sequence, and then set
  // any control knobs they need.
  ibex_icache_core_base_seq core_seq;
  ibex_icache_mem_resp_seq  mem_seq;

  // The number of transactions to run (passed to the core sequence). This gets randomised to
  // something sensible by default, but can be overridden by setting it before starting the
  // sequence.
  constraint num_trans_c { num_trans inside {[800:1000]}; }

  virtual task pre_start();
    `uvm_create_on(core_seq, p_sequencer.core_sequencer_h)
    `uvm_create_on(mem_seq, p_sequencer.mem_sequencer_h)

    // Unlike the other sequences, the core sequence has a finite number of items. Set that to our
    // number of transactions here.
    core_seq.num_trans = num_trans;

    if (prev_sequence != null) begin
      // If there was a previous sequence, pass it down to core_seq and mem_seq
      core_seq.prev_sequence = prev_sequence.core_seq;
      mem_seq.prev_sequence = prev_sequence.mem_seq;

      // If the new memory sequence will change mem_err_shift, we need to tell the core to
      // invalidate at the start of its sequence.
      if (cfg.mem_agent_cfg.mem_err_shift != mem_err_shift) begin
        core_seq.must_invalidate = 1'b1;
      end
    end

    // Write mem_err_shift into the config object (which the scoreboard and memory sequence will
    // both see)
    cfg.mem_agent_cfg.mem_err_shift = mem_err_shift;

    super.pre_start();
  endtask : pre_start

  virtual task body();
    fork
      // The core sequence blocks until it has run all its items.
      begin
        `DV_CHECK_RANDOMIZE_FATAL(core_seq)
        core_seq.start(p_sequencer.core_sequencer_h);
      end

      begin
        // This sequence will never end.
        `DV_CHECK_RANDOMIZE_FATAL(mem_seq)
        mem_seq.start(p_sequencer.mem_sequencer_h);
      end
    join_any

    // The core sequence has finished. Kill all the other sequences
    mem_seq.kill();

  endtask : body

  // Clear any interface signals that must be cleared before resetting the DUT.
  virtual task reset_ifs();
    core_seq.reset_ifs();
  endtask

endclass : ibex_icache_base_vseq
