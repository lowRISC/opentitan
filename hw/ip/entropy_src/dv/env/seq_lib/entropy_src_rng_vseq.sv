// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "entropy_src_base_rng_seq.sv"

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;

  `uvm_object_utils(entropy_src_rng_vseq)

  `uvm_object_new

  push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH) m_csrng_pull_seq;
  entropy_src_base_rng_seq                                              m_rng_push_seq;

  task software_read_seed();
    int seeds_found;
    `uvm_info(`gfn, "CSR Thread: Reading seed via SW", UVM_FULL)
    ral.entropy_control.es_route.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.entropy_control));
    // Wait for data to arrive for TL consumption via the ENTROPY_DATA register
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));
    ral.entropy_control.es_route.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.entropy_control));

    // read all available seeds
    do begin
      do_entropy_data_read(.seeds_found(seeds_found));
    end while (seeds_found > 0);
    `uvm_info(`gfn, "CSR Thread: Seed read Successfully", UVM_HIGH)
  endtask

  task enable_dut();
    `uvm_info(`gfn, "CSR Thread: Enabling DUT", UVM_MEDIUM)
    ral.conf.enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.conf));
  endtask

  //
  // The csr_access seq task executes all csr accesses for enabling/disabling the DUT as needed,
  // clearing assertions
  //
  task csr_access_seq();
    // Explicitly enable the DUT
    enable_dut();
    #(cfg.sim_duration/2);
    software_read_seed();
    #(cfg.sim_duration/2);
  endtask

  task body();
    super.body();

    // Create rng host sequence
    m_rng_push_seq = entropy_src_base_rng_seq::type_id::create("m_rng_push_seq");

    // Create csrng host sequence
    m_csrng_pull_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
        type_id::create("m_csrng_pull_seq");

    m_rng_push_seq.hard_mtbf = cfg.hard_mtbf;
    m_rng_push_seq.soft_mtbf = cfg.soft_mtbf;

    // m_csrng_pull_seq.num_trans = cfg.seed_cnt;
    // TODO: Enhance seq to work for hardware or software entropy consumer

    // Start sequences
    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
      begin
        csr_access_seq();
        // Once the CSR access is done, we can shut down everything else
        // Note: the CSRNG agent needs to be completely shut down before
        // shutting down the the AST/RNG.  Otherwise the CSRNG pull agent
        // will stall waiting for entropy.
        `uvm_info(`gfn, "Stopping CSRNG seq", UVM_LOW)
        m_csrng_pull_seq.stop(.hard(1));
        m_csrng_pull_seq.wait_for_sequence_state(UVM_FINISHED);
        `uvm_info(`gfn, "Stopping RNG seq", UVM_LOW)
        m_rng_push_seq.stop(.hard(0));
        m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
        `uvm_info(`gfn, "Exiting test body.", UVM_LOW)
      end
    join
  endtask : body

endclass : entropy_src_rng_vseq
