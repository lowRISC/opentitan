// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests any alerts not acheivable by the entropy_src_rng test
// At this time this is just the es_bus_cmp_alert.
//
// Please see previous revisions of this test to find routines for
// testing other recoverable alerts

class entropy_src_alert_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_alert_vseq)

  `uvm_object_new

  push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)        m_rng_push_seq;
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH) m_csrng_pull_seq;

  int window_size = 512;

  task pre_start();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg.dut_cfg, cfg.dut_cfg.fips_window_size == window_size;)
    super.pre_start();
  endtask

  task test_es_bus_cmp_alert();
    // We need two matching outputs. The first Startup seed will take twice as much data
    // and so will be different from the others.
    int num_reqs = 3;
    bit alert_val;

    // Create and rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");

    // Rememeber that the startup seed requires twice as many samples
    m_rng_push_seq.num_trans = (num_reqs + 1) * window_size/entropy_src_pkg::RNG_BUS_WIDTH;

    // Use a randomly generated but fixed rng_val through this test to make the entropy bus
    // value keep stable to induce the es_bus_cmp_alert
    `DV_CHECK_STD_RANDOMIZE_FATAL(rng_val)
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end

    // Create csrng host sequence
    m_csrng_pull_seq = push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
         type_id::create("m_csrng_pull_seq");
    m_csrng_pull_seq.num_trans = num_reqs;

    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value('0));

    enable_dut();

    fork
      // Start sequences
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
    join

    cfg.clk_rst_vif.wait_clks(10);

    csr_rd(.ptr(ral.recov_alert_sts.es_bus_cmp_alert), .value(alert_val));
    `DV_CHECK_EQ(alert_val, 1)

  endtask // test_es_bus_cmp_alert

  task body();

    // Test es_bus_cmp alert
    test_es_bus_cmp_alert();

  endtask : body

endclass : entropy_src_alert_vseq
