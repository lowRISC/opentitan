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

  virtual task entropy_src_init();
    int hi_thresh, lo_thresh;

    super.entropy_src_init();

    // TODO: RepCnt and RepCntS thresholds
    // TODO: Separate sigmas for bypass and FIPS operation
    // TODO: cfg for threshold_rec per_line arguments

    // AdaptP thresholds
    m_rng_push_seq.threshold_rec(cfg.fips_window_size, entropy_src_base_rng_seq::AdaptP, 0,
                                 cfg.adaptp_sigma, lo_thresh, hi_thresh);
    ral.adaptp_hi_thresholds.fips_thresh.set(hi_thresh[15:0]);
    ral.adaptp_lo_thresholds.fips_thresh.set(lo_thresh[15:0]);
    m_rng_push_seq.threshold_rec(cfg.bypass_window_size, entropy_src_base_rng_seq::AdaptP, 0,
                                 cfg.adaptp_sigma, lo_thresh, hi_thresh);
    ral.adaptp_hi_thresholds.bypass_thresh.set(hi_thresh[15:0]);
    ral.adaptp_lo_thresholds.bypass_thresh.set(lo_thresh[15:0]);
    csr_update(.csr(ral.adaptp_hi_thresholds));
    csr_update(.csr(ral.adaptp_lo_thresholds));

    // Bucket thresholds
    m_rng_push_seq.threshold_rec(cfg.fips_window_size, entropy_src_base_rng_seq::Bucket, 0,
                                 cfg.bucket_sigma, lo_thresh, hi_thresh);
    ral.bucket_thresholds.fips_thresh.set(hi_thresh[15:0]);
    m_rng_push_seq.threshold_rec(cfg.bypass_window_size, entropy_src_base_rng_seq::Bucket, 0,
                                 cfg.bucket_sigma, lo_thresh, hi_thresh);
    ral.bucket_thresholds.bypass_thresh.set(hi_thresh[15:0]);
    csr_update(.csr(ral.bucket_thresholds));

    // TODO: Markov DUT is currently cofigured for per_line operation (see Issue #9759)
    m_rng_push_seq.threshold_rec(cfg.fips_window_size, entropy_src_base_rng_seq::Markov, 1,
                                 cfg.markov_sigma, lo_thresh, hi_thresh);
    ral.markov_hi_thresholds.fips_thresh.set(hi_thresh[15:0]);
    ral.markov_lo_thresholds.fips_thresh.set(lo_thresh[15:0]);
    m_rng_push_seq.threshold_rec(cfg.bypass_window_size, entropy_src_base_rng_seq::Markov, 1,
                                 cfg.markov_sigma, lo_thresh, hi_thresh);
    ral.markov_hi_thresholds.bypass_thresh.set(hi_thresh[15:0]);
    ral.markov_lo_thresholds.bypass_thresh.set(lo_thresh[15:0]);
    csr_update(.csr(ral.markov_hi_thresholds));
    csr_update(.csr(ral.markov_lo_thresholds));
  endtask

  //
  // The csr_access seq task executes all csr accesses for enabling/disabling the DUT as needed,
  // clearing assertions
  //
  task csr_access_seq();
    // Explicitly enable the DUT
    enable_dut();
    #(cfg.sim_duration);
  endtask

  task pre_start();
    //
    // The DUT thresholds can be configured in coordination with the expected noise properties of
    // the RNG (which can also be parametrized to introduce bias or other non-idealities).  However
    // the RNG sequence then needs to be constructed before initializing the DUT, so that we can
    // query it for recommended thresholds when calling entropy_src_init().   So these seqeunces
    // are constructed before calling super.pre_start()
    //

    // Create rng host sequence
    m_rng_push_seq = entropy_src_base_rng_seq::type_id::create("m_rng_push_seq");

    // Create csrng host sequence
    m_csrng_pull_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
        type_id::create("m_csrng_pull_seq");

    m_rng_push_seq.hard_mtbf = cfg.hard_mtbf;
    m_rng_push_seq.soft_mtbf = cfg.soft_mtbf;

    super.pre_start();
  endtask

  task body();
    super.body();
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
