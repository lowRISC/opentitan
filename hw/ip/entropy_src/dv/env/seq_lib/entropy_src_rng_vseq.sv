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

  // Scheduled time for next unexpected reconfig event;
  // This time is exponentially distributed to yield an average period between
  // reconfig events of cfg.mean_unexpected_reconfig_period
  realtime sched_reconfig_time;

  // Scheduled time for randomized alert event;
  // This time is exponentially distributed to yield an average period between
  // reconfig events of cfg.mean_random_alert_period
  realtime sched_csr_alert_time;

  rand err_code_test_val_e csr_alert_value;

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

  virtual task entropy_src_init(entropy_src_dut_cfg newcfg=cfg.dut_cfg);
    int hi_thresh, lo_thresh;

    // TODO: RepCnt and RepCntS thresholds
    // TODO: Separate sigmas for bypass and FIPS operation
    // TODO: cfg for threshold_rec per_line arguments

    if (!newcfg.default_ht_thresholds) begin
      // AdaptP thresholds
      m_rng_push_seq.threshold_rec(newcfg.fips_window_size, adaptp_ht, 0,
                                   newcfg.adaptp_sigma, lo_thresh, hi_thresh);
      ral.adaptp_hi_thresholds.fips_thresh.set(hi_thresh[15:0]);
      ral.adaptp_lo_thresholds.fips_thresh.set(lo_thresh[15:0]);
      m_rng_push_seq.threshold_rec(newcfg.bypass_window_size, adaptp_ht, 0,
                                   newcfg.adaptp_sigma, lo_thresh, hi_thresh);
      ral.adaptp_hi_thresholds.bypass_thresh.set(hi_thresh[15:0]);
      ral.adaptp_lo_thresholds.bypass_thresh.set(lo_thresh[15:0]);
      csr_update(.csr(ral.adaptp_hi_thresholds));
      csr_update(.csr(ral.adaptp_lo_thresholds));

      // Bucket thresholds
      m_rng_push_seq.threshold_rec(newcfg.fips_window_size, bucket_ht, 0,
                                   newcfg.bucket_sigma, lo_thresh, hi_thresh);
      ral.bucket_thresholds.fips_thresh.set(hi_thresh[15:0]);
      m_rng_push_seq.threshold_rec(newcfg.bypass_window_size, bucket_ht, 0,
                                   newcfg.bucket_sigma, lo_thresh, hi_thresh);
      ral.bucket_thresholds.bypass_thresh.set(hi_thresh[15:0]);
      csr_update(.csr(ral.bucket_thresholds));

      // TODO: Markov DUT is currently cofigured for per_line operation (see Issue #9759)
      m_rng_push_seq.threshold_rec(newcfg.fips_window_size, markov_ht, 1,
                                   newcfg.markov_sigma, lo_thresh, hi_thresh);
      ral.markov_hi_thresholds.fips_thresh.set(hi_thresh[15:0]);
      ral.markov_lo_thresholds.fips_thresh.set(lo_thresh[15:0]);
      m_rng_push_seq.threshold_rec(newcfg.bypass_window_size, markov_ht, 1,
                                   newcfg.markov_sigma, lo_thresh, hi_thresh);
      ral.markov_hi_thresholds.bypass_thresh.set(hi_thresh[15:0]);
      ral.markov_lo_thresholds.bypass_thresh.set(lo_thresh[15:0]);
      csr_update(.csr(ral.markov_hi_thresholds));
      csr_update(.csr(ral.markov_lo_thresholds));
    end

    // configure the rest of the variables afterwards so that sw_regupd & module_enable
    // get written last
    super.entropy_src_init(newcfg);

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

    if ((cfg.dut_cfg.sw_regupd == 0) && (ral.sw_regupd.sw_regupd.get() == 0)) begin
      // Take this opportunity to test the sw_regupd register
      // Even though the module is disabled, the reconfig should not work
      random_reconfig();
      check_reconfig();
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
      if(ral.entropy_control.es_type.get_mirrored_value() == MuBi4True) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut);
        cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);
        reinit_dut();
      end
    end

    if (intr_status[FatalErr]) begin
      `uvm_info(`gfn, "starting shutdown", UVM_MEDIUM)
      // Gracefully stop the indefinite push and pull sequences, which
      // tend to raise endless objections after a hard reset.
      shutdown_indefinite_seqs();
      `uvm_info(`gfn, "SEQs SHUTDOWN applying hard reset", UVM_MEDIUM)
      apply_reset(.kind("HARD"));
      // Relaunch the push and pull sequences
      start_indefinite_seqs();
      // Restart the DUT with a new configuration
      random_reconfig();
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

  function void randomize_unexpected_config_time();
    if (cfg.mean_rand_reconfig_time > 0) begin
      sched_reconfig_time = randomize_failure_time(cfg.mean_rand_reconfig_time);
      // randomize_failure_time uses negative values to communicate errors
      `DV_CHECK_FATAL(sched_reconfig_time >= 0, "Failed to schedule reconfig event")
    end else begin
      // Use a negative value here to communicate no scheduled events
      sched_reconfig_time = -1;
    end
  endfunction

  function void randomize_csr_alert_time();
    if (cfg.mean_rand_csr_alert_time > 0) begin
      sched_csr_alert_time = randomize_failure_time(cfg.mean_rand_csr_alert_time);
      // randomize_failure_time uses negative values to communicate errors
      `uvm_info(`gfn, $sformatf("sched_csr_alert_time: %g", sched_csr_alert_time), UVM_LOW)
      `DV_CHECK_FATAL(sched_csr_alert_time >= 0, "Failed to schedule CSR alert event")
    end else begin
      // Use a negative value here to communicate no scheduled events
      sched_csr_alert_time = -1;
    end
  endfunction

  // A task to test the regupd and auto-lock regwen features.
  // Copies the existing env_cfg (with existing knobs)
  // and randomizes it to yield a new random configuration,
  // which it then applies to the DUT.
  //
  // If the Reg-locking features are working properly this
  // should have no effect
  task random_reconfig();
     entropy_src_dut_cfg altcfg;
    `uvm_info(`gfn, "Randomly reconfiguring DUT", UVM_HIGH)
    altcfg = new cfg.dut_cfg;

    `DV_CHECK_RANDOMIZE_FATAL(altcfg);
    altcfg.default_ht_thresholds = 1;
    `uvm_info(`gfn, altcfg.convert2string(), UVM_HIGH)
    entropy_src_init(altcfg);
  endtask

  task check_reconfig();
    string lockable_conf_regs [] = '{
        "conf", "entropy_control", "health_test_windows", "repcnt_thresholds", "repcnts_thresholds",
        "adaptp_hi_thresholds", "adaptp_lo_thresholds", "bucket_thresholds", "markov_hi_thresholds",
        "markov_lo_thresholds", "fw_ov_control", "observe_fifo_thresh"
    };
    foreach (lockable_conf_regs[i]) begin
      bit [TL_DW - 1:0] val;
      uvm_reg csr = ral.get_reg_by_name(lockable_conf_regs[i]);
      val = csr.get();
    end
  endtask

  task start_indefinite_seqs();
    fork
      // Thread 1 of 2: run the RNG push sequencer
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      // Thread 2 or 2: run the CSRNG pull sequencer
      // If the DUT is supposed to start in BOOT mode,
      // send a signal to reenable the DUT in continuous mode
      // after receiving one CSRNG seed.
      begin
        if (cfg.dut_cfg.route_software == MuBi4False &&
            cfg.dut_cfg.fips_enable == MuBi4False) begin
          // Notify the CSR access thread after the single boot mode seed has been received
          m_csrng_pull_seq_single.start(p_sequencer.csrng_sequencer_h);
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut);
          cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);
          // restart the DUT in continuous mode
          do_reenable = 1;
        end
        // Collect all post boot mode seeds in indefinite mode
        m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
      end
    join_none
  endtask

  task body();
    bit [TL_DW - 1:0] fw_ov_value;
    super.body();
    randomize_unexpected_config_time();
    randomize_csr_alert_time();
    // Start sequences in the background
    start_indefinite_seqs();
    fork
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
          // Check if it is time to attempt another random reconfig event
          if (sched_reconfig_time > 0 && $realtime() > sched_reconfig_time) begin
            random_reconfig();
            randomize_unexpected_config_time();
            check_reconfig();
          end
          // Check if it is time for a randomized csr-driven alert
          // (generated via the ERR_CODE_TEST register)
          // Note: these alerts are only checked when enabled.
          if (sched_csr_alert_time > 0 && $realtime() > sched_csr_alert_time &&
              ral.module_enable.module_enable.get_mirrored_value() == MuBi4True) begin
            string msg;
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(csr_alert_value);
            msg = $sformatf("Generating alert via ERR_CODE_TEST with err_code %d", csr_alert_value);
            `uvm_info(`gfn, msg, UVM_LOW)
            csr_wr(.ptr(ral.err_code_test.err_code_test), .value(csr_alert_value));
            randomize_csr_alert_time();
          end
        end
        `uvm_info(`gfn, "Exiting interrupt loop", UVM_HIGH)
      end
      // Inject entropy if
      // 1. the DUT config requires it, or
      // 2. the env config wants to inject it spuriously
      if (cfg.spurious_inject_entropy ||
          ((cfg.dut_cfg.fw_over_enable == MuBi4True)
            && (cfg.dut_cfg.fw_read_enable == MuBi4True)) ) begin
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
