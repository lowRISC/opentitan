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

  // Should we generate ECC errors in the underlying SRAM objects?
  bit enable_ecc_errors = 0;

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

  // ECC sequences. The arrays are created in pre_start and are nonempty if ECC errors are enabled.
  ibex_icache_ecc_base_seq  ecc_tag_seqs[];
  ibex_icache_ecc_base_seq  ecc_data_seqs[];

  // The number of transactions to run (passed to the core sequence). This gets randomised to
  // something sensible by default, but can be overridden by setting it before starting the
  // sequence.
  constraint num_trans_c { num_trans inside {[800:1000]}; }

  virtual task pre_start();
    super.pre_start();

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

    // If enable_ecc_errors then create any ECC sequences we need (one for each sequencer in
    // p_sequencer.ecc_tag_sequencers and p_sequencer.ecc_data_sequencers).
    ecc_tag_seqs = new[enable_ecc_errors ? p_sequencer.ecc_tag_sequencers.size() : 0];
    foreach (ecc_tag_seqs[i]) begin
      `uvm_create_on(ecc_tag_seqs[i], p_sequencer.ecc_tag_sequencers[i])
    end
    ecc_data_seqs = new[enable_ecc_errors ? p_sequencer.ecc_data_sequencers.size() : 0];
    foreach (ecc_data_seqs[i]) begin
      `uvm_create_on(ecc_data_seqs[i], p_sequencer.ecc_data_sequencers[i])
    end
  endtask : pre_start

  virtual task body();
    fork
      // The core sequence blocks until it has run all its items.
      begin
        `DV_CHECK_RANDOMIZE_FATAL(core_seq)
        core_seq.start(p_sequencer.core_sequencer_h);
      end

      // These sequences will never end. We wrap them all up together in a fork/join so that we can
      // fork/join_none any ECC sequences (which yield immediately so that we can start them in a
      // loop), but still have a process that never yields, to use as a child for the surrounding
      // fork/join_any.
      fork
        begin
          `DV_CHECK_RANDOMIZE_FATAL(mem_seq)
          mem_seq.start(p_sequencer.mem_sequencer_h);
        end
        foreach (ecc_tag_seqs[i]) begin
          start_ecc_body(ecc_tag_seqs[i], p_sequencer.ecc_tag_sequencers[i]);
        end
        foreach (ecc_data_seqs[i]) begin
          start_ecc_body(ecc_data_seqs[i], p_sequencer.ecc_data_sequencers[i]);
        end
      join
    join_any

    // The core sequence has finished. Kill all the other sequences
    mem_seq.kill();
    foreach (ecc_tag_seqs[i]) ecc_tag_seqs[i].kill();
    foreach (ecc_data_seqs[i]) ecc_data_seqs[i].kill();

  endtask : body

  // Randomize and then run a given (never ending) ECC sequence on the given sequencer. Returns
  // immediately (so you can start sequences in a loop).
  protected task start_ecc_body(ibex_icache_ecc_base_seq seq, ibex_icache_ecc_sequencer sqr);
    `DV_CHECK_RANDOMIZE_FATAL(seq);
    fork begin
      seq.start(sqr);
    end join_none
  endtask

endclass : ibex_icache_base_vseq
