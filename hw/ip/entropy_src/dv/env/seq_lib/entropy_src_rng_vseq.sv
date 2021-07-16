// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_rng_vseq)

  `uvm_object_new

  task body();
    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    // TODO: num_reqs > 4 (fifo_full). Will drop without reqs, need to predict.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reqs, num_reqs inside {[1:4]};)
    m_rng_push_seq.num_trans = num_reqs * entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rng_val);
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);

    // Create and start csrng host sequence
    m_csrng_pull_seq = push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::type_id::
         create("m_csrng_pull_seq");

    m_csrng_pull_seq.num_trans = num_reqs;
    m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
    // TODO: Enhance seq to work for hardware or software entropy consumer
  endtask : body

endclass : entropy_src_rng_vseq
