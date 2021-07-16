// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_smoke_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_smoke_vseq)

  `uvm_object_new

  task body();
    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      rng_val = i % 16;
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));

    // Read and check entropy
    for (int i = 0; i < entropy_src_pkg::CSRNG_BUS_WIDTH/TL_DW/2; i++) begin
      csr_rd_check(.ptr(ral.entropy_data), .compare_value(INCR_ENTROPY_LO));
      csr_rd_check(.ptr(ral.entropy_data), .compare_value(INCR_ENTROPY_HI));
    end

    // Ensure entropy_valid interrupt bit set
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b1));

    // Clear entropy_valid interrupt bit
    csr_wr(.ptr(ral.intr_state), .value(1'b1));

    // Ensure entropy_valid interrupt bit cleared
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b0));

  endtask : body

endclass : entropy_src_smoke_vseq
