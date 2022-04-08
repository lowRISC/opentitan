// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "entropy_src_base_rng_seq.sv"

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;

  `uvm_object_utils(entropy_src_rng_vseq)

  push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH) m_csrng_pull_seq;
  // For use in non-FIPS mode
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)            m_csrng_pull_seq_single;
  entropy_src_base_rng_seq                                              m_rng_push_seq;

  rand uint dly_to_access_intr;
  rand uint dly_to_access_alert_sts;
  rand uint dly_to_insert_entropy;
  rand uint dly_to_reenable_dut;
  rand int  fw_ov_insert_per_seed;
  rand bit  do_check_ht_diag;
  rand bit  do_clear_ht_alert;

  int do_background_procs;

  // Signal to start and stop the RNG when it becomes halted in boot/bypass modes
  int do_reenable = 0;

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0                   :/ 1,
      [1      :100]       :/ 5,
      [101    :10_000]    :/ 3
    };
  }

  constraint dly_to_access_alert_sts_c {
    dly_to_access_alert_sts dist {
      0                   :/ 1,
      [1      :100]       :/ 5,
      [101    :10_000]    :/ 3
    };
  }

  constraint dly_to_insert_entropy_c {
    dly_to_insert_entropy dist {
      0                   :/ 1,
      [1      :100]       :/ 3,
      [101    :1000]      :/ 2,
      [1001   :10_000]    :/ 1
    };
  }

  constraint dly_to_reenable_dut_c {
    dly_to_reenable_dut dist {
      [1      :100]       :/ 3,
      [101    :1000]      :/ 2,
      [1001   :10_000]    :/ 1
    };
  }

  constraint fw_ov_insert_per_seed_c {
    fw_ov_insert_per_seed inside { 16, 32, 64, 128, 256 };
  }

  constraint do_check_ht_diag_c {
    do_check_ht_diag dist {
      0 :/ cfg.do_check_ht_diag_pct,
      1 :/ 100 - cfg.do_check_ht_diag_pct
    };
  }

  `uvm_object_new

  task software_read_seed();
    int seeds_found;
    `uvm_info(`gfn, "CSR Thread: Reading seed via SW", UVM_FULL)
    ral.entropy_control.es_route.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.entropy_control));
    // Wait for data to arrive for TL consumption via the ENTROPY_DATA register
    poll();
    ral.entropy_control.es_route.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.entropy_control));

    // read all available seeds
    do begin
      do_entropy_data_read(.bundles_found(seeds_found));
    end while (seeds_found > 0);
    `uvm_info(`gfn, "CSR Thread: Seed read Successfully", UVM_HIGH)
  endtask

  task enable_dut();
    `uvm_info(`gfn, "CSR Thread: Enabling DUT", UVM_MEDIUM)
    ral.module_enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.module_enable));
  endtask

  virtual task entropy_src_init();
    int hi_thresh, lo_thresh;


    // TODO: RepCnt and RepCntS thresholds
    // TODO: Separate sigmas for bypass and FIPS operation
    // TODO: cfg for threshold_rec per_line arguments

    if (!cfg.default_ht_thresholds) begin
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
    end

    // configure the rest of the variables afterwards so that sw_regupd & module_enable
    // get written last
    super.entropy_src_init();

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

    m_csrng_pull_seq_single = push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
        type_id::create("m_csrng_pull_seq_single");
    m_csrng_pull_seq_single.num_trans = 1;

    m_rng_push_seq.hard_mtbf = cfg.hard_mtbf;
    m_rng_push_seq.soft_mtbf = cfg.soft_mtbf;

    do_background_procs = 1'b1;

    super.pre_start();
  endtask

  // Clears the module_enable signal and at the same time clears the
  // any interrupts that may have become stale as a result of the disable
  // operation.
  // TODO (documentation): Make sure this get an issue to be sure it goes into SW
  task reinit_dut(bit switch_to_fips_mode = 0);

    csr_wr(.ptr(ral.module_enable.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Disabling the module will clear the error state,
    // as well as the observe and entropy_data FIFOs
    // Clear all three related interupts here
    csr_wr(.ptr(ral.intr_state), .value(32'h7));

    // Optionally switch the device into FIPS mode for the remainder of the test
    if (switch_to_fips_mode) begin
      csr_wr(.ptr(ral.conf.fips_enable), .value(MuBi4True));
    end

    csr_wr(.ptr(ral.recov_alert_sts.es_main_sm_alert), .value(1'b1));
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(do_check_ht_diag)
    if (do_check_ht_diag) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_alert_sts)
      cfg.clk_rst_vif.wait_clks(dly_to_access_alert_sts);
      // read all health check values
      `uvm_info(`gfn, "Checking_ht_values", UVM_HIGH)
      check_ht_diagnostics();
      `uvm_info(`gfn, "HT value check complete", UVM_HIGH)
    end

    enable_dut();

  endtask

  task clear_ht_alert();
    bit  alert_sts;
    // Health check failures are coincident with an alert, which needs to also be cleared
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr);
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);
    csr_rd(.ptr(ral.recov_alert_sts.es_main_sm_alert), .value(alert_sts));
    if (alert_sts) begin
      `uvm_info(`gfn, "Clearing ES SM Alerts", UVM_HIGH)
      `uvm_info(`gfn, "Identified main_sm alert", UVM_HIGH)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_alert_sts)
      cfg.clk_rst_vif.wait_clks(dly_to_access_alert_sts);
      reinit_dut();
    end
  endtask

  task process_interrupts();
    bit [TL_DW - 1:0] intr_status, clear_intr;
    `uvm_info(`gfn, "process interrupts", UVM_HIGH)

    // avoid zero delay loop during reset
    wait(!cfg.under_reset);
    // read interrupt
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);
    csr_rd(.ptr(ral.intr_state), .value(intr_status));

    if (intr_status != 0) begin
      `uvm_info(`gfn, $sformatf("Handling Interrupts: %02h", intr_status), UVM_FULL)
    end else begin
      return;
    end

    if (intr_status[HealthTestFailed]) begin
      // TODO: I think there is a distinction between health test failure and alert.
      //       We may be able to economize (or diversify) this test by only doing this on alerts.
      `uvm_info(`gfn, "Health test failure detected", UVM_HIGH)
      clear_ht_alert();
      // Note: clear_ht_alert may purge the internal fifos.
      //       Don't service any of the other interrupts without first querying the interrupt status
      //       again
      csr_rd(.ptr(ral.intr_state), .value(intr_status));
    end

    if (intr_status[ObserveFifoReady]) begin
      int bundles_found;
      // Read all currently available data
      do_entropy_data_read(.source(TlSrcObserveFIFO),
                           .bundles_found(bundles_found));
    end

    if (intr_status[EntropyValid]) begin
      int bundles_found;
      do_entropy_data_read(.source(TlSrcEntropyDataReg),
                           .bundles_found(bundles_found));
      `uvm_info(`gfn, $sformatf("Found %d entropy_data bundles", bundles_found), UVM_HIGH)
      if(cfg.type_bypass == MuBi4True) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut);
        cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);
        reinit_dut();
      end
    end

    `uvm_info(`gfn, "Interrupt handler complete", UVM_FULL)

  endtask

  task shutdown_indefinite_seqs();
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
  endtask


  task body();
    bit [TL_DW - 1:0] fw_ov_value;
    super.body();
    // Start sequences
    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        if (cfg.route_software == MuBi4False && cfg.fips_enable == MuBi4False) begin
          // Notify the CSR access thread after the single boot mode seed has been received
          m_csrng_pull_seq_single.start(p_sequencer.csrng_sequencer_h);
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut);
          cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);
          do_reenable = 1;
        end
        // Collect all post boot mode seeds in indefinite mode
        m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
      end
      begin
        `uvm_info(`gfn, "Starting interrupt loop", UVM_HIGH)
        while (do_background_procs) begin
          process_interrupts();
          // If a NON-FIPS-to-FIPS re-enable is needed, coordinate the
          // re-enable process with the interrupt handler to avoid
          // I/O conflicts (e.g. reading I/O queues while the DUT is being
          // disabled.) Such activities lead to alerts which are very hard
          // to predict generally, and should be validated in the alert
          // tests.
          if (do_reenable) begin
            do_reenable = 0;
            reinit_dut(1);
          end
        end
        `uvm_info(`gfn, "Exiting interrupt loop", UVM_HIGH)
      end
      // Inject entropy if
      // 1. the DUT config requires it, or
      // 2. the env config wants to inject it spuriously
      if (cfg.spurious_inject_entropy ||
          ((cfg.fw_over_enable == MuBi4True) && (cfg.fw_read_enable == MuBi4True)) ) begin
        while (do_background_procs) begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fw_ov_insert_per_seed);
          ral.fw_ov_sha3_start.fw_ov_insert_start.set(MuBi4True);
          csr_update(.csr(ral.fw_ov_sha3_start));
          for(int i = 0; i < fw_ov_insert_per_seed; i++) begin
            `DV_CHECK_STD_RANDOMIZE_FATAL(fw_ov_value);
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_insert_entropy);
            cfg.clk_rst_vif.wait_clks(dly_to_insert_entropy);
            `uvm_info(`gfn, $sformatf("injecting entropy: %08x", fw_ov_value), UVM_FULL)
            ral.fw_ov_wr_data.set(fw_ov_value);
            csr_update(.csr(ral.fw_ov_wr_data));
          end
          ral.fw_ov_sha3_start.fw_ov_insert_start.set(MuBi4False);
          csr_update(.csr(ral.fw_ov_sha3_start));
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_insert_entropy);
          cfg.clk_rst_vif.wait_clks(dly_to_insert_entropy);
        end
      end
      begin
        csr_access_seq();
        `uvm_info(`gfn, "Shutting down push_pull seqs", UVM_LOW)
        shutdown_indefinite_seqs();
        `uvm_info(`gfn, "Stopping background procs", UVM_LOW)
        do_background_procs = 1'b0;
      end
    join
    `uvm_info(`gfn, "Body complete", UVM_LOW)
  endtask : body

endclass : entropy_src_rng_vseq
