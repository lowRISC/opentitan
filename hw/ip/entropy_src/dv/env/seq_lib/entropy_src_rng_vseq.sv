// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_rng_vseq)

  `uvm_object_new

  // TODO: This variable currently overlaps with cfg.seed_cnt
  rand int num_seeds_requested;

  task body();
    // Create rng host sequence
    m_rng_push_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");

    // Create csrng host sequence
    m_csrng_pull_seq = push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::type_id::
         create("m_csrng_pull_seq");
    m_csrng_pull_seq.num_trans = num_seeds_requested;
    // TODO: Enhance seq to work for hardware or software entropy consumer

    // Start sequences
    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
        m_rng_push_seq.stop();
      end
    join
  endtask : body

endclass : entropy_src_rng_vseq
