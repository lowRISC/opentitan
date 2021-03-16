// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_rng_vseq)

  `uvm_object_new

  uint             num_trans, i;
  rand bit [3:0]   rng_val, rng_val_q[$];
  bit [31:0] 	   val;
  push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)   m_rng_push_seq;

  task body();
    // Set entropy_src controls
    csr_wr(.ptr(ral.entropy_control), .value({cfg.type_bypass, cfg.route_software}));
    // Enable entropy_src
    csr_wr(.ptr(ral.conf), .value(cfg.enable));

    // Create and start host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    num_trans = 96;
    m_rng_push_seq.num_trans = num_trans + 1; // +1 per hardware requirement
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rng_val);
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));

    // Read entropy_data register (384/32=12 times)
    for (int i = 0; i < (4 * num_trans) / 32; i++) begin
      csr_rd(.ptr(ral.entropy_data), .value(val));
    end

    // TODO: Enhance seq to randomize num_trans and work for hardware or software entropy consumer
  endtask : body

endclass : entropy_src_rng_vseq
