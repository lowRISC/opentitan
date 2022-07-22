// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "entropy_src_base_rng_seq.sv"

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;

  `uvm_object_utils(entropy_src_rng_vseq)

  push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH) m_csrng_pull_seq;
  entropy_src_base_rng_seq                                              m_rng_push_seq;

  rand uint dly_to_access_intr;
  rand uint dly_to_access_alert_sts;
  rand uint dly_to_insert_entropy;
  rand uint dly_to_reenable_dut;
  rand int  fw_ov_insert_per_seed;
  rand bit  do_check_ht_diag;
  rand bit  do_clear_ht_alert;

  // flags for coordinating between threads
  bit do_background_procs, continue_sim, reset_needed;

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

  task enable_dut();
    `uvm_info(`gfn, "CSR Thread: Enabling DUT", UVM_MEDIUM)
    csr_wr(.ptr(ral.module_enable.module_enable), .value(prim_mubi_pkg::MuBi4True));
  endtask

  virtual task entropy_src_init(entropy_src_dut_cfg newcfg=cfg.dut_cfg, bit do_disable=1'b0);
    int hi_thresh, lo_thresh;

    if (do_disable) begin
      ral.module_enable.set(MuBi4False);
      csr_update(.csr(ral.module_enable));
    end

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
    // Note there is no need to disable the dut again for the remaining registers
    // it has already been done above.
    super.entropy_src_init(.newcfg(newcfg), .do_disable(1'b0));

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

    m_rng_push_seq.hard_mtbf = cfg.hard_mtbf;
    m_rng_push_seq.soft_mtbf = cfg.soft_mtbf;

    super.pre_start();
  endtask

  // Clears the module_enable signal and at the same time clears the
  // any interrupts that may have become stale as a result of the disable
  // operation.
  // TODO (documentation): Make sure this get an issue to be sure it goes into SW
  task reinit_dut(bit switch_to_fips_mode = 0);

    // Flag to force SW update to fire.
    // We'll only use this if we have gaps in coverage.
    bit check_sw_update_explicit = 1'b0;

    csr_wr(.ptr(ral.module_enable.module_enable), .value(MuBi4False));
    // Disabling the module will clear the error state,
    // as well as the observe and entropy_data FIFOs
    // Clear all three related interupts here
    csr_wr(.ptr(ral.intr_state), .value(32'h7));

    // Optionally switch the device into FIPS mode for the remainder of the test
    if (switch_to_fips_mode) begin
      `uvm_info(`gfn, "SWITCHING to FIPS mode", UVM_MEDIUM)
      csr_wr(.ptr(ral.conf.fips_enable), .value(MuBi4True));
    end

    // Clear all recoverable alerts
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'hffff_ffff));
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(do_check_ht_diag)
    if (do_check_ht_diag) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_alert_sts)
      cfg.clk_rst_vif.wait_clks(dly_to_access_alert_sts);
      // read all health check values
      `uvm_info(`gfn, "Checking_ht_values", UVM_HIGH)
      check_ht_diagnostics();
      `uvm_info(`gfn, "HT value check complete", UVM_HIGH)
    end

    if (check_sw_update_explicit &&
        (cfg.dut_cfg.sw_regupd == 0) && (ral.sw_regupd.sw_regupd.get() == 0)) begin
      entropy_src_dut_cfg altcfg;
      altcfg=cfg.dut_cfg;
      `DV_CHECK_RANDOMIZE_FATAL(altcfg)
      entropy_src_init(altcfg);
      check_reconfig();
      // Don't bother updating cfg.dut_cfg for this rare case.  Updating the dut_cfg is
      // useful for logging, but it may not be worth the complexity here.
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
      bit [TL_DW - 1:0] err_code_val;
      `uvm_info(`gfn, "starting shutdown", UVM_MEDIUM)
      // Gracefully stop the indefinite push and pull sequences, which
      // tend to raise endless objections after a hard reset.
      do_background_procs = 0;
      // check the err_codes
      csr_rd(.ptr(ral.err_code), .value(err_code_val));
      reset_needed = 1;
    end

    `uvm_info(`gfn, "Interrupt handler complete", UVM_FULL)

  endtask

  task shutdown_indefinite_seqs();
    // Once the CSR access is done, we can shut down everything else
    // Note: the CSRNG agent needs to be completely shut down before
    // shutting down the the AST/RNG.  Otherwise the CSRNG pull agent
    // will stall waiting for entropy
    `uvm_info(`gfn, "Confirming that CSRNG indefinite seq has started", UVM_HIGH)
    `uvm_info(`gfn, $sformatf("STATE: %s", m_csrng_pull_seq.get_sequence_state().name), UVM_HIGH)
    m_csrng_pull_seq.wait_for_sequence_state(UVM_BODY);

    `uvm_info(`gfn, "Stopping CSRNG seq", UVM_LOW)
    m_csrng_pull_seq.stop(.hard(1));
    //p_sequencer.csrng_sequencer_h.stop_sequences();
    `uvm_info(`gfn, "Stopping CSRNG sequencer", UVM_LOW)
    m_csrng_pull_seq.wait_for_sequence_state(UVM_FINISHED);
    `uvm_info(`gfn, "Stopping RNG seq", UVM_LOW)
    m_rng_push_seq.stop(.hard(0));
    m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
    `uvm_info(`gfn, "SEQs SHUTDOWN applying CSRNG reset", UVM_MEDIUM)
    apply_reset(.kind("CSRNG_ONLY"));
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

  task check_reconfig();
    string lockable_conf_regs [] = '{
        "conf", "entropy_control", "health_test_windows", "repcnt_thresholds", "repcnts_thresholds",
        "adaptp_hi_thresholds", "adaptp_lo_thresholds", "bucket_thresholds", "markov_hi_thresholds",
        "markov_lo_thresholds", "fw_ov_control", "observe_fifo_thresh"
    };
    foreach (lockable_conf_regs[i]) begin
      bit [TL_DW - 1:0] val;
      uvm_reg csr = ral.get_reg_by_name(lockable_conf_regs[i]);
      csr_rd(.ptr(csr), .value(val));
    end
  endtask

  task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask

  task start_indefinite_seqs();

    // Create a new csrng host sequence
    //
    // (Since we are frequently interrupting the CSRNG sequence mid-item, it
    // seems to often not like to be restarted, and the old one will often just
    // stay in the UVM_FINISHED state, so we create a new sequence item each time)
    m_csrng_pull_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
        type_id::create("m_csrng_pull_seq");

    fork
      // Thread 1 of 2: run the RNG push sequencer
      begin
        m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      end

      // Thread 2 or 2: run the CSRNG pull sequencer
      begin
        m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
      end
    join_none
  endtask

  // A thread-task to continuously inject entropy
  //
  // To be started if:
  // A. the DUT config requires it, or
  // B. the env config wants to inject it spuriously (to test that it has
  //    to side effects)
  //
  // This task is fairly simple it only does two things:
  // 1. It writes to fw_ov_wr_data
  // 2. As needed, it turns the SHA3 conditioning on and off.
  //    TODO: check that the behavior of this thread matches what is expected
  //    For boot mode.
  //
  // Runs until the timer thread halts background operations
  task entropy_inject_thread();
    bit do_inject, injection_mandatory;
    bit [TL_DW - 1:0] fw_ov_value;

    injection_mandatory = ((cfg.dut_cfg.fw_over_enable == MuBi4True) &&
                           (cfg.dut_cfg.fw_read_enable == MuBi4True));
    do_inject           = injection_mandatory || cfg.spurious_inject_entropy;

    if (do_inject) begin
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
  endtask

  // A thread task to continously handle interrupts
  // runs until the timer thread
  task interrupt_handler_thread();
    `uvm_info(`gfn, "Starting interrupt loop", UVM_HIGH)
    while (do_background_procs) begin
      process_interrupts();
      // If a NONFIPS-to-FIPS re-enable is needed, coordinate the
      // re-enable process with the interrupt handler to avoid
      // I/O conflicts (e.g. reading I/O queues while the DUT is being
      // disabled.) Such activities lead to alerts which are very hard
      // to predict generally, and should be validated in the alert
      // tests.
      if (do_reenable) begin
        do_reenable = 0;
        `uvm_info(`gfn, "Reinitializing DUT in continuous mode", UVM_MEDIUM)
        reinit_dut(1);
        `uvm_info(`gfn, "Reinit complete", UVM_HIGH)
       end
    end
    `uvm_info(`gfn, "Exiting interrupt loop", UVM_HIGH)
  endtask

  // A thread to prompt the simulation to end at the correct time.
  // 1. Sets continue_sim to 0 when simulation is due to end
  // 2. Stops background processes
  task master_timer_thread();
    realtime delta = cfg.sim_duration - $realtime();
    // Assumes that continue_sim has already
    // been set to 1
    if (delta > 0) begin
      #(delta);
      do_background_procs = 0;
      continue_sim = 0;
    end
  endtask

  // Keep an eye on the number of SEEDS received on the
  // CSRNG interface, and trigger a re-start if the
  // DUT has probably hung because when in Boot Mode
  // it can only generate one seed.
  task reinit_monitor_thread();
    bit boot_mode_csrng;
    mubi4_t fips_enable, es_route;

    wait(cfg.under_reset == 0);
    csr_rd(.ptr(ral.conf.fips_enable), .value(fips_enable));
    csr_rd(.ptr(ral.entropy_control.es_route), .value(es_route));

    boot_mode_csrng = fips_enable != MuBi4True &&
                      es_route != MuBi4True;

    if (boot_mode_csrng && do_background_procs) begin
      fork : isolation_fork
        fork
          begin
            m_csrng_pull_seq.wait_for_items_processed(1);
            // Notify the interrtupt/CSR access thread after the single boot mode seed has been
            // received
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut)
            cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);
            // restart the DUT in continuous mode
            `uvm_info(`gfn, "Triggering reinit from BOOT to Continuous Mode", UVM_MEDIUM)
            do_reenable = 1;
          end
          // Give up if we get a call to stop
          wait(!do_background_procs);
        join_any
        disable fork;
      join
    end
  endtask

  task forced_alert_thread();
    realtime delta;
    string msg;
    while (do_background_procs) begin
      randomize_csr_alert_time();
      if (sched_csr_alert_time > 0) begin
        delta = sched_csr_alert_time - $realtime();
        fork : isolation_fork
          fork
            #(delta);
            wait(!do_background_procs);
          join_any
          disable fork;
        join
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(csr_alert_value);
        msg = $sformatf("Generating alert via ERR_CODE_TEST with err_code %d", csr_alert_value);
        `uvm_info(`gfn, msg, UVM_MEDIUM)
        csr_wr(.ptr(ral.err_code_test.err_code_test), .value(csr_alert_value));
        // This may generate an alert.  Most codes, except code 22 (mismatched counter primitives)
        // only generate alerts when enabled.  Code 22 always generates an alert.
      end
    end
  endtask

  task reconfig_timer_thread();
    realtime delta;
    randomize_unexpected_config_time();
    if (sched_reconfig_time > 0) begin
      delta = (sched_reconfig_time - $realtime());
      fork : isolation_fork
        fork
          #(delta);
          wait(!do_background_procs);
        join_any
        disable fork;
      join
      // Stop other background procs (if they haven't been already)
      // This will prompt a reconfig.
      do_background_procs = 0;
    end
  endtask

  task body();

    do_background_procs = 1;
    continue_sim = 1;
    reset_needed = 0;

    // Start sequences in the background
    start_indefinite_seqs();

    // Do the first DUT initialization as usual
    super.body();

    fork
      master_timer_thread();

      while (continue_sim) begin
        bit regwen;
        // For use when doing random reconfigs
        entropy_src_dut_cfg altcfg;

        // Explicitly enable the DUT
        enable_dut();

        // In addition to the CSRNG and RNG sequences
        // the following four threads will run until
        // do_background_procs == 0
        fork
          entropy_inject_thread();
          interrupt_handler_thread();
          forced_alert_thread();
          reconfig_timer_thread();
          reinit_monitor_thread();
        join

        if(!continue_sim) break;

        // Resuming single thread operation

        //
        // Resetting and/or reconfiguring before the next loop.
        //
        // The CSRNG agent is often an important part of DUT reinitialization it tells us when
        // it is safe to reconfigure the entropy source from BOOT mode into CONTINUOUS mode.
        // That said, regardless of whether we resetting we should turn off the CSRNG/RNG
        // sequences.
        //
        // Meanwhile, this shutdown of the CSRNG agent is even more important, as
        // the CSRNG monitor can cause things to hang or give spurious fatal errors
        // if the monitor is reset without stopping the sequence first.
        // (TODO: Examine this more closely & file an issue)
        //

        `uvm_info(`gfn, "Shutting down push_pull seqs", UVM_LOW)
        shutdown_indefinite_seqs();

        if (reset_needed) begin
          `uvm_info(`gfn, "SEQs SHUTDOWN applying hard reset", UVM_MEDIUM)
          apply_reset(.kind("HARD"));
          post_apply_reset(.reset_kind("HARD"));
          wait(cfg.under_reset == 0);
        end

        // Make a new random dut configuration according
        // to our current DUT constraints
        altcfg=cfg.dut_cfg;
        `DV_CHECK_RANDOMIZE_FATAL(altcfg)
        entropy_src_init(altcfg);
        // Capture the current DUT settings in cfg.dut_cfg
        // This presents the results of the update
        // to the scoreboard for review.
        check_reconfig();
        csr_rd(.ptr(ral.regwen.regwen), .value(regwen));
        if (regwen || reset_needed) begin
          cfg.dut_cfg = altcfg;
          `uvm_info(`gfn, "DUT Reconfigured", UVM_LOW)
          `uvm_info(`gfn, cfg.dut_cfg.convert2string(), UVM_LOW)
        end

        // Now we can clear the reset flag.
        reset_needed = 0;
        // Also, don't schedule a reinit yet (for BOOT-to-Continuous mode switching)
        do_reenable = 0;

        // We start the CSRNG sequence _here_ (and not earlier as) it needs
        // to know the current configuration for whether or not the DUT is
        // in boot mode.
        //
        // Ideally, however, we would like to start it before reconfiguring
        // the DUT for checking issues with order of bring-up etc.
        // Running the restart after the DUT has been configured is not the
        // most stressful test.
        `uvm_info(`gfn, "RESTARTING RNG/CSRNG SEQS", UVM_MEDIUM)
        start_indefinite_seqs();
      end
    join

    // Simulation complete
    //
    // Stop the CSRNG/RNG sequences, and then exit to
    // the base class vseq for cleanup.

    shutdown_indefinite_seqs();
    `uvm_info(`gfn, "Body complete", UVM_LOW)
  endtask : body

endclass : entropy_src_rng_vseq
