// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "entropy_src_base_rng_seq.sv"

// rng test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;

  `uvm_object_utils(entropy_src_rng_vseq)

  push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH) m_csrng_pull_seq;
  entropy_src_base_rng_seq                                              m_rng_push_seq;
  entropy_src_xht_base_device_seq                                       m_xht_seq;

  // Tracks the number of CSRNG seeds seen by the m_csrng_pull_seq
  // just before enabling.
  int csrng_pull_seq_seed_offset = 0;

  rand uint dly_to_access_intr;
  rand uint dly_to_access_alert_sts;
  rand uint dly_to_insert_entropy;
  rand uint dly_to_reenable_dut;
  rand int  fw_ov_insert_per_seed;

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

  bit interrupt_handler_active = 0;

  // List of states to specfically hit for main_sm transition coverage
  localparam int NumRareMainFsmStates = 12;

  entropy_src_main_sm_pkg::state_e [NumRareMainFsmStates - 1:0] rare_fsm_states = {
     entropy_src_main_sm_pkg::StartupPass1,
     entropy_src_main_sm_pkg::StartupFail1,
     entropy_src_main_sm_pkg::StartupHTStart,
     entropy_src_main_sm_pkg::FWInsertMsg,
     entropy_src_main_sm_pkg::BootPostHTChk,
     entropy_src_main_sm_pkg::ContHTStart,
     entropy_src_main_sm_pkg::FWInsertStart,
     entropy_src_main_sm_pkg::Sha3MsgDone,
     entropy_src_main_sm_pkg::Sha3Prep,
     entropy_src_main_sm_pkg::Sha3Process,
     entropy_src_main_sm_pkg::Sha3Valid,
     entropy_src_main_sm_pkg::AlertState
  };

  // A checklist vector with each bit corresponding to each of the rare_fsm_states above.
  // To force all rare transitions to Idle simply initialize the rare_state_to_idle_checklist to
  // all zeros.  For transitions which are frequently found in regression the forced transition
  // can be skipped by initializing the corresponding bit to 1.
  //
  // If needed, this scheme can in principle be expanded to other rare transitions (for instance
  // to AlertState) by creating another checklist variable and updating the task
  // targeted_transition_thread()

  bit [NumRareMainFsmStates - 1:0] rare_state_to_idle_checklist = '{default: 1'b0};
  bit [NumRareMainFsmStates - 1:0] rare_state_to_idle_backdoor = '{
    NumRareMainFsmStates - 3: 1'b1, // StartupHTStart
    default: 1'b0
  };

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0                   :/ 1,
      [1      :100]       :/ 8,
      [101    :10_000]    :/ 1
    };
  }

  constraint dly_to_access_alert_sts_c {
    dly_to_access_alert_sts dist {
      0                   :/ 1,
      [1      :100]       :/ 8,
      [101    :10_000]    :/ 1
    };
  }

  constraint dly_to_insert_entropy_c {
    dly_to_insert_entropy dist {
      0                   :/ 5,
      [1      :10]        :/ 15,
      [11     :100]       :/ 5,
      [101    :1000]      :/ 1
    };
  }

  constraint dly_to_reenable_dut_c {
    dly_to_reenable_dut dist {
      [1      :10]       :/ 10,
      [101    :100]      :/ 3,
      [1001   :1000]     :/ 1
    };
  }

  constraint fw_ov_insert_per_seed_c {
    fw_ov_insert_per_seed inside { 16, 32, 64, 128, 256 };
  }

  `uvm_object_new

  virtual task enable_dut();
    // Before restarting, get the current seed count
    // of the csrng_pull seq, so that we can identify when the
    // next seed has been obtained
    if (`gmv(ral.module_enable.module_enable) != MuBi4True) begin
      csrng_pull_seq_seed_offset = m_csrng_pull_seq.items_processed;
      do_reenable = 0;
    end
    super.enable_dut();
  endtask

  virtual task disable_dut();
    // In case an undetected failure is encountered, reset the RNG on disable. This will clear any
    // simulated failures during random reconfig events even if the DUT has not detected them with
    // an alert.
    // NOTE: This should not change the average frequency of simulated RNG failures, given that the
    // instantaneous likelihood of failure is designed to be independent of history.
    m_rng_push_seq.reset_rng();
    super.disable_dut();
  endtask


  virtual task try_apply_base_configuration(entropy_src_dut_cfg newcfg,
                                            realtime pause,
                                            output bit completed);

    int hi_thresh, lo_thresh;
    mubi4_t threshold_scope = newcfg.ht_threshold_scope;

    completed = 0;

    if (!newcfg.default_ht_thresholds) begin
      // AdaptP thresholds
      `uvm_info(`gfn, "Setting ADAPTP thresholds", UVM_DEBUG)
      m_rng_push_seq.threshold_rec(newcfg.fips_window_size, adaptp_ht,
                                   threshold_scope != MuBi4True,
                                   newcfg.adaptp_sigma, lo_thresh, hi_thresh);
      ral.adaptp_hi_thresholds.fips_thresh.set(hi_thresh[15:0]);
      ral.adaptp_lo_thresholds.fips_thresh.set(lo_thresh[15:0]);
      m_rng_push_seq.threshold_rec(newcfg.bypass_window_size, adaptp_ht,
                                   threshold_scope != MuBi4True,
                                   newcfg.adaptp_sigma, lo_thresh, hi_thresh);
      ral.adaptp_hi_thresholds.bypass_thresh.set(hi_thresh[15:0]);
      ral.adaptp_lo_thresholds.bypass_thresh.set(lo_thresh[15:0]);
      csr_update(.csr(ral.adaptp_hi_thresholds));
      csr_update(.csr(ral.adaptp_lo_thresholds));

      // Bucket thresholds
      `uvm_info(`gfn, "Setting BUCKET thresholds", UVM_DEBUG)
      m_rng_push_seq.threshold_rec(newcfg.fips_window_size, bucket_ht, 0,
                                   newcfg.bucket_sigma, lo_thresh, hi_thresh);
      ral.bucket_thresholds.fips_thresh.set(hi_thresh[15:0]);
      m_rng_push_seq.threshold_rec(newcfg.bypass_window_size, bucket_ht, 0,
                                   newcfg.bucket_sigma, lo_thresh, hi_thresh);
      ral.bucket_thresholds.bypass_thresh.set(hi_thresh[15:0]);
      csr_update(.csr(ral.bucket_thresholds));

      // Markov Thresholds
      `uvm_info(`gfn, "Setting MARKOV thresholds", UVM_DEBUG)
      m_rng_push_seq.threshold_rec(newcfg.fips_window_size, markov_ht,
                                   threshold_scope != MuBi4True,
                                   newcfg.markov_sigma, lo_thresh, hi_thresh);
      ral.markov_hi_thresholds.fips_thresh.set(hi_thresh[15:0]);
      ral.markov_lo_thresholds.fips_thresh.set(lo_thresh[15:0]);
      m_rng_push_seq.threshold_rec(newcfg.bypass_window_size, markov_ht,
                                   threshold_scope != MuBi4True,
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
    super.try_apply_base_configuration(.newcfg(newcfg), .pause(pause), .completed(completed));
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

    m_csrng_pull_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
        type_id::create("m_csrng_pull_seq");

    m_xht_seq = entropy_src_xht_base_device_seq::type_id::create("m_xht_seq");

    // Don't configure the DUT in dut_init (which is called in pre-start).  Instead wait until
    // we reach the main body() task, where we can handle any configuration alerts.
    do_entropy_src_init = 1'b0;

    super.pre_start();
  endtask

  // Clears the module_enable signal and at the same time clears the
  // any interrupts that may have become stale as a result of the disable
  // operation.
  task reinit_dut(bit switch_to_fips_mode = 0);

    // Flag to force SW update to fire.
    // We'll only use this if we have gaps in coverage.
    bit check_sw_update_explicit = 1'b0;

    wait_no_outstanding_access();
    if (!do_background_procs) return;

    if (!`gmv(ral.me_regwen.me_regwen) || !`gmv(ral.sw_regupd.sw_regupd)) begin
      `uvm_info(`gfn, "DUT is permanently locked, reset required", UVM_MEDIUM);
      do_background_procs = 0;
      return;
    end

    disable_dut();

    // Optionally switch the device into FIPS mode for the remainder of the test
    if (switch_to_fips_mode) begin
      `uvm_info(`gfn, "SWITCHING to FIPS mode", UVM_MEDIUM)
      csr_wr(.ptr(ral.conf.fips_enable), .value(MuBi4True));
      if (`gmv(ral.entropy_control.es_route) == MuBi4True) begin
        csr_wr(.ptr(ral.entropy_control.es_type), .value(MuBi4False));
      end
    end

    if (check_sw_update_explicit &&
        (cfg.dut_cfg.sw_regupd == 0) && (ral.sw_regupd.sw_regupd.get() == 0)) begin
      bit completed, regwen;

      entropy_src_dut_cfg altcfg;
      altcfg=cfg.dut_cfg;
      `DV_CHECK_RANDOMIZE_FATAL(altcfg)
      entropy_src_init(.newcfg(altcfg), .completed(completed), .regwen(regwen));
      check_reconfig();
      // Don't bother updating cfg.dut_cfg for this rare case.  Updating the dut_cfg is
      // useful for logging, but it may not be worth the complexity here.
    end

    wait_no_outstanding_access();
    enable_dut();

  endtask

  task process_interrupts();
    bit [TL_DW - 1:0] intr_status;
    bit               interrupt_shutdown = 0;

    `uvm_info(`gfn, "process interrupts", UVM_DEBUG)

    // avoid zero delay loop during reset
    wait(!cfg.under_reset);

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);

    `uvm_info(`gfn, "Asserting interrupt_handler_active", UVM_DEBUG)
    interrupt_handler_active = 1;
    csr_rd(.ptr(ral.intr_state), .value(intr_status));

    if (intr_status != 0) begin
      `uvm_info(`gfn, $sformatf("Handling Interrupts: %02h", intr_status), UVM_FULL)
    end else begin
      interrupt_handler_active = 0;
      return;
    end

    // handle the Observe FIFO first as that will have no impact on other features
    if (intr_status[ObserveFifoReady]) begin
      int bundles_found;
      `uvm_info(`gfn, "Reading observe FIFO", UVM_DEBUG)
      // Read all currently available data
      do_entropy_data_read(.source(TlSrcObserveFIFO),
                           .bundles_found(bundles_found));
      `uvm_info(`gfn, $sformatf("Found %d observe FIFO bundles", bundles_found), UVM_FULL)
    end

    // Reading the ENTROPY_DATA reg may be slightly more impactful than the Observe
    // FIFO, as a restart may be needed.
    if (intr_status[EntropyValid]) begin
      int bundles_found;
      `uvm_info(`gfn, "Reading entropy_data", UVM_DEBUG)
      do_entropy_data_read(.source(TlSrcEntropyDataReg),
                           .bundles_found(bundles_found));
      `uvm_info(`gfn, $sformatf("Found %d entropy_data bundles", bundles_found), UVM_FULL)
      if (`gmv(ral.entropy_control.es_type)  == MuBi4True ||
          `gmv(ral.conf.fips_enable)         == MuBi4False) begin
        do_reenable = 1;
      end
    end

    // There is no risk of deactivating the DUT now.
    `uvm_info(`gfn, "Clearing interrupt_handler_active", UVM_DEBUG)
    interrupt_handler_active = 0;

    // If a health test error is detected, break the loop and reconfigure
    if (intr_status[HealthTestFailed]) begin
      `uvm_info(`gfn, "Health test failure detected", UVM_HIGH)
      // Notify all the other threads that it's time for corrective action
      interrupt_shutdown = 1;
      // We'll manage the HT failure once the v-sequence collapses to single
      // threaded mode.
    end

    if (intr_status[FatalErr]) begin
      bit [TL_DW - 1:0] err_code_val;
      `uvm_info(`gfn, "starting shutdown", UVM_MEDIUM)
      // Check the err_codes, just to query the scoreboard.
      csr_rd(.ptr(ral.err_code), .value(err_code_val));
      // Regardless of the source the remedy is always a reset.
      reset_needed = 1;
      // Notify all the other threads that it's time for corrective action
      interrupt_shutdown = 1;
    end

    if(interrupt_shutdown) begin
      // Sure, something bad happened. But if nothing else is going on, let the DUT stew a bit.
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut);
      // Wait for either do_background_procs = 0 or dly_to_reenable_dut
      `DV_SPINWAIT_EXIT(cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);,
                        wait(!do_background_procs);)
      do_background_procs = 0;
    end

    `uvm_info(`gfn, "Interrupt handler complete", UVM_FULL)
  endtask

  task shutdown_indefinite_seqs();
    // Once the CSR access is done, we can shut down everything else
    // Note: the CSRNG agent needs to be completely shut down before
    // shutting down the AST/RNG.  Otherwise the CSRNG pull agent
    // will stall waiting for entropy
    `uvm_info(`gfn, "Confirming that CSRNG indefinite seq has started", UVM_HIGH)
    `uvm_info(`gfn, $sformatf("STATE: %s", m_csrng_pull_seq.get_sequence_state().name), UVM_HIGH)
    m_csrng_pull_seq.wait_for_sequence_state(UVM_BODY);

    `uvm_info(`gfn, "Stopping XHT sequencer", UVM_LOW)
    p_sequencer.xht_sequencer.stop_sequences();

    `uvm_info(`gfn, "Stopping CSRNG seq", UVM_LOW)
    m_csrng_pull_seq.stop(.hard(0));
    `uvm_info(`gfn, "Stopping RNG seq", UVM_LOW)
    m_rng_push_seq.stop(.hard(0));
    `uvm_info(`gfn, "SEQs SHUTDOWN applying CSRNG reset", UVM_MEDIUM)
    apply_reset(.kind("CSRNG_ONLY"));
    `uvm_info(`gfn, "Waiting for SEQs finished", UVM_MEDIUM)
    m_csrng_pull_seq.wait_for_sequence_state(UVM_FINISHED);
    m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
    `uvm_info(`gfn, "SEQs shutdown", UVM_LOW)

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
    string msg;
    if (cfg.mean_rand_csr_alert_time > 0) begin
      sched_csr_alert_time = randomize_failure_time(cfg.mean_rand_csr_alert_time);
      // randomize_failure_time uses negative values to communicate errors
      msg = $sformatf("sched_csr_alert_time: %0.2f ms", sched_csr_alert_time/1ms);
      `uvm_info(`gfn, msg, UVM_FULL)
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
        "markov_lo_thresholds", "fw_ov_control", "observe_fifo_thresh", "alert_threshold"
    };
    foreach (lockable_conf_regs[i]) begin
      bit [TL_DW - 1:0] val;
      uvm_reg csr = ral.get_reg_by_name(lockable_conf_regs[i]);
      csr_rd(.ptr(csr), .value(val));
    end
  endtask

  task post_start();
    super.post_start();
  endtask

  task start_indefinite_seqs();

    // Create a new csrng host sequence
    //
    // (Since we are frequently interrupting the CSRNG sequence mid-item, it
    // seems to often not like to be restarted, and the old one will often just
    // stay in the UVM_FINISHED state, so we create a new sequence item each time)

    fork
        m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
        m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
        if (!cfg.xht_only_default_rsp) begin
          m_xht_seq.start(p_sequencer.xht_sequencer);
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
  //
  // Runs until the timer thread halts background operations
  task entropy_inject_thread();
    bit do_inject, injection_mandatory;
    bit [TL_DW - 1:0] fw_ov_value;

    injection_mandatory = ((cfg.dut_cfg.fw_over_enable == MuBi4True) &&
                           (cfg.dut_cfg.fw_read_enable == MuBi4True));
    do_inject           = injection_mandatory || cfg.spurious_inject_entropy;


    `uvm_info(`gfn, "Entropy injection thread waiting for DUT to be enabled", UVM_MEDIUM)
    csr_spinwait(.ptr(ral.module_enable.module_enable),
                 .exp_data(MuBi4True),
                 .backdoor(1));

    `uvm_info(`gfn, "Starting entropy injection thread", UVM_LOW)

    if (do_inject) begin
      while (do_background_procs) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fw_ov_insert_per_seed);
        ral.fw_ov_sha3_start.fw_ov_insert_start.set(MuBi4True);
        csr_update(.csr(ral.fw_ov_sha3_start));
        for (int i = 0; i < fw_ov_insert_per_seed; i++) begin
          if (!do_background_procs) break;
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

    `uvm_info(`gfn, "Exiting entropy injection thread", UVM_LOW)

  endtask

  // A thread task to continously handle interrupts
  // runs until the timer thread
  task interrupt_handler_thread();
    `uvm_info(`gfn, "Starting interrupt loop", UVM_LOW)
    while (do_background_procs) begin
      process_interrupts();
      // If a NONFIPS-to-FIPS re-enable is needed, coordinate the
      // re-enable process with the interrupt handler to avoid
      // I/O conflicts (e.g. reading I/O queues while the DUT is being
      // disabled.) Such activities lead to alerts which are very hard
      // to predict generally, and should be validated in the alert
      // tests.
      if (do_background_procs && do_reenable) begin
        do_reenable = 0;
        `uvm_info(`gfn, "Reinitializing DUT in continuous mode", UVM_MEDIUM)
        reinit_dut(1);
        `uvm_info(`gfn, "Reinit complete", UVM_HIGH)
       end
    end
    `uvm_info(`gfn, "Exiting interrupt loop", UVM_LOW)
  endtask

  // A thread to prompt the simulation to end at the correct time.
  // 1. Sets continue_sim to 0 when simulation is due to end
  // 2. Stops background processes
  task main_timer_thread();
    realtime delta = cfg.sim_duration - $realtime();
    `uvm_info(`gfn, "Starting main timer", UVM_LOW)

    // Assumes that continue_sim has already
    // been set to 1
    if (delta > 0) begin
      `DV_SPINWAIT_EXIT(#(delta);, wait(~continue_sim))
    end
    do_background_procs = 0;
    continue_sim = 0;
    `uvm_info(`gfn, "Exiting main timer", UVM_LOW)
  endtask

  // Helper task to targeted_transition_thread.
  //
  // When trying to precisely time a register write to trigger a particular FSM transition, it is
  // necessary to temporarily remove any tl_agent delays.  This function removes delays on the
  // a_valid signal before writing the desired register.  Once the write is complete the delays
  // are restored.
  //
  // Note: It is important to use a frontdoor csr_wr, as opposed to a csr_poke, because such though
  // backdoor writes will realize the desired transition they will not be captured by the tl_monitor
  // and will confuse the scoreboard.
  task immed_csr_wr(input uvm_object ptr, input uvm_reg_data_t value);
    bit use_seq_item_a_valid_delay_orig;
    int unsigned a_valid_delay_min_orig;
    int unsigned a_valid_delay_max_orig;

    // Back up the original tl_agent config
    use_seq_item_a_valid_delay_orig = cfg.m_tl_agent_cfg.use_seq_item_a_valid_delay;
    a_valid_delay_min_orig =  cfg.m_tl_agent_cfg.a_valid_delay_min;
    a_valid_delay_max_orig =  cfg.m_tl_agent_cfg.a_valid_delay_max;

    // Configure the tl_agent to issue the command immediately
    cfg.m_tl_agent_cfg.use_seq_item_a_valid_delay = 0;
    cfg.m_tl_agent_cfg.a_valid_delay_min = 0;
    cfg.m_tl_agent_cfg.a_valid_delay_max = 0;

    csr_wr(.ptr(ptr), .value(value));

    // Restore the CSR agent configurations
    cfg.m_tl_agent_cfg.use_seq_item_a_valid_delay = use_seq_item_a_valid_delay_orig;
    cfg.m_tl_agent_cfg.a_valid_delay_min = a_valid_delay_min_orig;
    cfg.m_tl_agent_cfg.a_valid_delay_max = a_valid_delay_max_orig;

  endtask

  // A thread to poll the state of the DUT and inject CSR events to stimulate uncovered transitions
  // One example BootPostHTCheck -> Idle
  task targeted_transition_thread();
    string msg;
    while(do_background_procs && continue_sim) begin
      bit [TL_DW - 1:0] val;

      if (&rare_state_to_idle_checklist) begin
        break;
      end

      // In order to not interrupt the interrupt handler (which would cause unpredictable observe
      // FIFO underflow alerts in the DUT and crash the sim) we only perform targeted shutdown when
      // the interrupt handler is not running.
      //
      // Wait until the interrupt handler is done (with a 1ms timeout) or one clock cycle, whichever
      // is longer.  In either case shutdown if a thread shutdown is requested
      fork
        if(interrupt_handler_active) begin
          `DV_WAIT(!interrupt_handler_active || !do_background_procs,
                   "Interrupt handler timed out", 1ms/1ns);
        end
        cfg.clk_rst_vif.wait_clks(1);
      join

      if (!do_background_procs || !continue_sim) break;

      for (int i=0; i < NumRareMainFsmStates; i++) begin
        if (cfg.fsm_tracking_vif.next_state == rare_fsm_states[i]) begin

          if (!rare_state_to_idle_checklist[i]) begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(induce_targeted_transition, cfg);
            if (cfg.induce_targeted_transition) begin
              msg = $sformatf("Forcing disable from state %s", rare_fsm_states[i].name());
              `uvm_info(`gfn, msg, UVM_HIGH)
              // First immediately disable the device, with an ASAP frontdoor write and if needed
              // a  preceeding backdoor write (timed to trigger in the next cycle, for states that
              // almost always follow CSR operations such as enable signals)
              // Finally call disable_dut() to clean things up properly.
              if (rare_state_to_idle_backdoor[i]) begin
                cfg.clk_rst_vif.wait_clks(1);
                csr_poke(.ptr(ral.module_enable), .value({28'h0, MuBi4False}));
              end
              immed_csr_wr(.ptr(ral.module_enable), .value({28'h0, MuBi4False}));
              disable_dut();
              do_background_procs = 0;
              rare_state_to_idle_checklist[i] = 1'b1;
              break;
            end
          end
          // If other types of transitions need to be stimulated they can be executed here.
        end
      end
    end

    `uvm_info(`gfn, $sformatf("rare enable mask: %01x",  rare_state_to_idle_checklist), UVM_HIGH)

  endtask

  // Keep an eye on the number of SEEDS received on the
  // CSRNG interface, and trigger a re-start if the
  // DUT has probably hung because when in Boot Mode
  // it can only generate one seed.
  task reinit_monitor_thread();
    bit boot_mode_csrng;
    logic [MuBi4Width-1:0] fips_enable, es_route;

    `uvm_info(`gfn, "Starting re-init monitor", UVM_LOW)

    wait(cfg.under_reset == 0);
    csr_rd(.ptr(ral.conf.fips_enable), .value(fips_enable));
    csr_rd(.ptr(ral.entropy_control.es_route), .value(es_route));

    // We don't need to monitor the CSRNG bus if nothing will be coming on it, or
    // if the DUT is already configured to output FIPS data.
    boot_mode_csrng = fips_enable != MuBi4True &&
                      es_route != MuBi4True;

    if (boot_mode_csrng && do_background_procs) begin
      `uvm_info(`gfn, "Waiting for CSRNG Seed", UVM_MEDIUM)
      `DV_SPINWAIT_EXIT(m_csrng_pull_seq.wait_for_items_processed(csrng_pull_seq_seed_offset + 1);,
                        wait (!do_background_procs))
      if(do_background_procs) begin
        // Notify the interrtupt/CSR access thread after the single boot mode seed has been
        // received
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_reenable_dut)
        `DV_SPINWAIT_EXIT(cfg.clk_rst_vif.wait_clks(dly_to_reenable_dut);,
                          wait (!do_background_procs))
        // restart the DUT in continuous mode
        `uvm_info(`gfn, "Triggering reinit from BOOT to Continuous Mode", UVM_MEDIUM)
        if (do_background_procs) do_reenable = 1;
      end
    end
    `uvm_info(`gfn, "Exiting re-init monitor", UVM_LOW)
  endtask

  task forced_alert_thread();
    realtime delta;
    string msg;

    if (cfg.mean_rand_csr_alert_time <= 0) begin
      `uvm_info(`gfn, "Skipping forced-alert thread", UVM_LOW)
      return;
    end

    `uvm_info(`gfn, "Starting forced-alert thread", UVM_LOW)

    while (do_background_procs) begin
      randomize_csr_alert_time();
      if (sched_csr_alert_time > 0) begin
        delta = sched_csr_alert_time - $realtime();
        `DV_SPINWAIT_EXIT(#(delta);, wait(!do_background_procs))
        if (do_background_procs) begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(csr_alert_value);
          msg = $sformatf("Generating alert via ERR_CODE_TEST with err_code %d", csr_alert_value);
          expect_fatal_alerts = 1'b1;
          `uvm_info(`gfn, msg, UVM_MEDIUM)
          csr_wr(.ptr(ral.err_code_test.err_code_test), .value(csr_alert_value));
          // This may generate an alert.  Most codes, except code 22 (mismatched counter primitives)
          // only generate alerts when enabled.  Code 22 always generates an alert.
        end
      end
    end
    `uvm_info(`gfn, "Exiting forced-alert thread", UVM_LOW)

  endtask

  task reconfig_timer_thread();
    realtime delta = -1, random_delta, timeout_delta, init_time;
    string  msg;

    init_time = $realtime();

    timeout_delta = !cfg.generates_seeds(mubi4_t'(`gmv(ral.entropy_control.es_route)),
                                         mubi4_t'(`gmv(ral.conf.entropy_data_reg_enable))) ?
                    cfg.max_silent_reconfig_time : -1;

    if (cfg.mean_rand_reconfig_time <= 0 && timeout_delta <= 0) begin
      `uvm_info(`gfn, "Skipping reconfig timer thread", UVM_LOW)
      return;
    end

    `uvm_info(`gfn, "Starting reconfig timer thread", UVM_LOW)

    randomize_unexpected_config_time();
    if (sched_reconfig_time > 0) begin
      random_delta = (sched_reconfig_time - init_time);
    end

    case ({random_delta > 0, timeout_delta > 0})
      2'b11: delta = random_delta < timeout_delta ? random_delta : timeout_delta;
      2'b10: delta = random_delta;
      2'b01: delta = timeout_delta;
      2'b00: delta = -1;
      default: delta = -1;
    endcase

    msg = $sformatf("random_delta: %0.2fms, timeout_delta: %0.2fms, delta: %0.2fms",
                    random_delta/1ms, timeout_delta/1ms, delta/1ms);
    `uvm_info(`gfn, msg, UVM_DEBUG)

    if(delta > 0) begin
      msg  = $sformatf("Schedling reconfig after %0.2f ms", delta/1ms);
      `uvm_info(`gfn, msg, UVM_MEDIUM)
      `DV_SPINWAIT_EXIT(#(delta);, wait(!do_background_procs);)
      if(!do_background_procs) begin
        msg  = $sformatf("Reconfig pre-empted after %0.2f ms", ($realtime()-init_time)/1ms);
        `uvm_info(`gfn, msg, UVM_MEDIUM)
      end
      // Stop other background procs (if they haven't been already)
      // This will prompt a reconfig
      do_background_procs = 0;
    end
    `uvm_info(`gfn, "Exiting reconfig timer thread", UVM_LOW)
  endtask

  // Make a new random dut configuration according
  // to our current DUT constraints
  task random_reconfig(bit do_reset);
    bit reconfig_complete;
    bit regwen;
    bit sw_locked = (`gmv(ral.sw_regupd.sw_regupd) == 0);

    int bad_mubi_cfg_pct_orig = cfg.dut_cfg.bad_mubi_cfg_pct;
    int preconfig_disable_pct_orig = cfg.dut_cfg.preconfig_disable_pct;
    entropy_src_dut_cfg altcfg=new cfg.dut_cfg;

    do begin
      string msg;

      if (do_reset) begin
        apply_reset(.kind("HARD_DUT_ONLY"));
        post_apply_reset(.reset_kind("HARD"));
      end
      wait(cfg.under_reset == 0);
      do_reenable = 0;

      `uvm_info(`gfn, "Generating new random config", UVM_MEDIUM)
      // Make a new copy of the DUT cfg.
      altcfg = new cfg.dut_cfg;
      `DV_CHECK_RANDOMIZE_FATAL(altcfg);
      if (!do_reset) begin
        // Don't change the ht_threshold_scope or window sizes without a reset otherwise the one-way
        // HT thresholds will not allow us to apply sensible ranges, and any following health tests
        // will likely fail.
        altcfg.bypass_window_size   = cfg.dut_cfg.bypass_window_size;
        altcfg.fips_window_size     = cfg.dut_cfg.fips_window_size;
        altcfg.ht_threshold_scope   = cfg.dut_cfg.ht_threshold_scope;
      end

      // Force the DUT to not absorb the new config (to test write protect), unless
      // the configuration explicitly says to disable before reconfiguring
      if(!altcfg.preconfig_disable) begin
        enable_dut();
      end

      entropy_src_init(.newcfg(altcfg),
                       .completed(reconfig_complete),
                       .regwen(regwen));
      if (!reconfig_complete) begin
        // Don't do any more bad MuBi's settings this round.
        `uvm_info(`gfn, "Disabling Bad Mubi settings for now", UVM_MEDIUM)
        cfg.dut_cfg.bad_mubi_cfg_pct = 0;
      end else begin
        // Capture the current DUT settings in cfg.dut_cfg
        // This presents the results of the update
        // to the scoreboard for review.
        check_reconfig();
      end
      // Even if the reconfig proceeded without an exception, we check to see
      // if there were any obstacles to configuration. If so configure again
      // after disabling and, if necessary, resetting the device.
      if (reconfig_complete && !regwen) begin
        cfg.dut_cfg.preconfig_disable_pct = 100;
        sw_locked = (`gmv(ral.sw_regupd.sw_regupd) == 0);
        // Force a reset if the device is currently locked via sw_regupd
        if (sw_locked) do_reset = 1;
      end
    end while (!(reconfig_complete && regwen) && continue_sim);

    check_reconfig();

    init_successful = 1;
    if (regwen || do_reset) begin
       `uvm_info(`gfn, "DUT Reconfigured", UVM_LOW)
       `uvm_info(`gfn, altcfg.convert2string(), UVM_LOW)
    end

    // Write the new config to dut_cfg
    cfg.dut_cfg = altcfg;

    // Restore modified knobs
    cfg.dut_cfg.bad_mubi_cfg_pct = bad_mubi_cfg_pct_orig;
    cfg.dut_cfg.preconfig_disable_pct = preconfig_disable_pct_orig;

    // Don't enable here, let the main loop do that explicitly
  endtask

  task body();

    do_background_procs = 1;
    continue_sim = 1;
    reset_needed = 0;

    // Start sequences in the background
    start_indefinite_seqs();

    fork
      main_timer_thread();
      while (continue_sim) begin
        bit regwen;
        do_background_procs = 1;
        reset_needed = 0;

        // If the initial configuration (in dut_init) failed, start with a reconfig.
        if (!init_successful) random_reconfig(0);

        `uvm_info(`gfn, "Launching event threads", UVM_LOW)

        // In addition to the CSRNG and RNG sequences
        // the following four threads will run until
        // do_background_procs == 0
        fork
          entropy_inject_thread();
          interrupt_handler_thread();
          reinit_monitor_thread();
          forced_alert_thread();
          reconfig_timer_thread();
          // Start the targetted transition thread, unless it is clear from the cfg that it will
          // never actually induce any transitions.
          if (cfg.induce_targeted_transition_pct != 0) begin
            targeted_transition_thread();
          end
          begin
            // Explicitly enable the DUT with no delay
            enable_dut();
          end
        join

        if(!continue_sim) break;
        `uvm_info(`gfn, "Resuming single thread operation", UVM_LOW)

        // Disable the DUT and get HT stats.
        disable_dut();

        //
        // Resetting and/or reconfiguring before the next loop.
        //
        random_reconfig(reset_needed);
        // Now we can clear the reset flag.
        reset_needed = 0;
        `uvm_info(`gfn, "Reconfig complete, resuming simulation", UVM_MEDIUM)

        // Also, don't schedule a reinit yet (for BOOT-to-Continuous mode switching)

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
