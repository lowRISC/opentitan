// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_rng_vseq)

  `uvm_object_new

  task body();
    // Create rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    // TODO: num_reqs > 4 (fifo_full). Will drop without reqs, need to predict.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reqs, num_reqs inside {[1:4]};)
    if (cfg.rng_bit_enable == prim_mubi_pkg::MuBi4True) begin
      m_rng_push_seq.num_trans = (4 * num_reqs *
           (entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH + 1));
    end
    else begin
      m_rng_push_seq.num_trans =  num_reqs *
           entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    end
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rng_val);
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end

    // Create csrng host sequence
    m_csrng_pull_seq = push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::type_id::
         create("m_csrng_pull_seq");
    m_csrng_pull_seq.num_trans = num_reqs;
    // TODO: Enhance seq to work for hardware or software entropy consumer

    // Start sequences 
    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
    join_none
  endtask : body

endclass : entropy_src_rng_vseq
