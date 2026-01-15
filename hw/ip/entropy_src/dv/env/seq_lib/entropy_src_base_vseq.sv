// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_base_vseq extends cip_base_vseq #(
    .RAL_T               (entropy_src_reg_block),
    .CFG_T               (entropy_src_env_cfg),
    .COV_T               (entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T (entropy_src_virtual_sequencer)
  );
  `uvm_object_utils(entropy_src_base_vseq)

  rand bit [`RNG_BUS_WIDTH-1:0]      rng_val;
  rand bit [NumEntropySrcIntr - 1:0] en_intr;
  rand bit  do_check_ht_diag;

  // various knobs to enable certain routines
  bit  do_entropy_src_init = 1'b1;
  bit  do_interrupt        = 1'b1;

  bit init_successful      = 1'b0;

  bit [15:0] path_err_val;

  virtual entropy_src_cov_if   cov_vif;


  constraint do_check_ht_diag_c {
    do_check_ht_diag dist {
      0 :/ cfg.do_check_ht_diag_pct,
      1 :/ 100 - cfg.do_check_ht_diag_pct
    };
  }

  `uvm_object_new

  task pre_start();
    cfg.otp_en_es_fw_read_vif.drive(.val(cfg.otp_en_es_fw_read));
    cfg.otp_en_es_fw_over_vif.drive(.val(cfg.otp_en_es_fw_over));

    if (!uvm_config_db#(virtual entropy_src_cov_if)::get
        (null, "*.env" , "entropy_src_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get entropy_src_cov_if from uvm_config_db"))
    end

    super.pre_start();

  endtask

  virtual task dut_init(string reset_kind = "HARD");
    int regwen;

    super.dut_init(.reset_kind(reset_kind));

    // Don't loop here trying to reconfigure (in case the configuration fails)
    // leave that to any derived tests that allow for configuration failures.
    if (do_entropy_src_init) begin
      entropy_src_init(.newcfg(cfg.dut_cfg), .completed(init_successful), .regwen(regwen));
    end
  endtask

  //
  // Most of the health check diagnostics are hard to read during the normal test.
  //
  // Since there is a delay between when data is received at the RNG interface and when
  // the health check completes, checking these registers during the usual test body can lead
  // to spurious scoreboarding errors.   We let the scoreboard check these all at the end of
  // the test instead.
  //
  task check_ht_diagnostics();
    int val;
    string stat_regs [] = '{
        "ht_watermark",
        "repcnt_total_fails", "repcnts_total_fails", "adaptp_hi_total_fails",
        "adaptp_lo_total_fails", "bucket_total_fails", "markov_hi_total_fails",
        "markov_lo_total_fails", "extht_hi_total_fails", "extht_lo_total_fails",
        "alert_summary_fail_counts", "alert_fail_counts", "extht_fail_counts"
    };
    foreach (stat_regs[i]) begin
      int val;
      uvm_reg csr = ral.get_reg_by_name(stat_regs[i]);
      csr_rd(.ptr(csr), .value(val));
    end

  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "CSRNG_ONLY") begin
      cfg.csrng_rst_vif.apply_reset();
    end else if (kind == "HARD_DUT_ONLY") begin
      super.apply_reset("HARD");
    end else begin
      super.apply_reset(kind);
      cfg.csrng_rst_vif.apply_reset();
    end
  endtask

  virtual task dut_shutdown();
    bit bundles_found;
    // check for pending entropy_src operations and wait for them to complete
    `uvm_info(`gfn, "Shutting down", UVM_LOW)

    `uvm_info(`gfn, "Disabling DUT", UVM_MEDIUM)
    disable_dut();

    `uvm_info(`gfn, "Checking diagnostics", UVM_MEDIUM)
    check_ht_diagnostics();
    `uvm_info(`gfn, "Clearing Alerts", UVM_MEDIUM)
    ral.recov_alert_sts.es_main_sm_alert.set(1'b0);
    csr_update(.csr(ral.recov_alert_sts));

    super.dut_shutdown();
  endtask

  // Abstract the method of enabling the dut, to potentially allow for
  // callbacks to be applied in the derived classes
  virtual task enable_dut();
    `uvm_info(`gfn, "Enabling DUT", UVM_MEDIUM)
    csr_wr(.ptr(ral.module_enable.module_enable), .value(prim_mubi_pkg::MuBi4True));
  endtask

  task disable_dut();
    bit [TL_DW - 1:0] regval;

    csr_wr(.ptr(ral.module_enable.module_enable), .value(MuBi4False));

    // Disabling the module will clear the error state,
    // as well as the observe and entropy_data FIFOs
    // Clear all interrupts here
    csr_wr(.ptr(ral.intr_state), .value(32'hf));

    // Check, but do not clear alert_sts, as the handlers for those conditions may need to see them.
    csr_rd(.ptr(ral.recov_alert_sts.es_main_sm_alert), .value(regval));

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(do_check_ht_diag)
    if (do_check_ht_diag) begin
      // read all health check values
      `uvm_info(`gfn, "Checking_ht_values", UVM_HIGH)
      check_ht_diagnostics();
      `uvm_info(`gfn, "HT value check complete", UVM_HIGH)
    end
  endtask

  // Helper function to entropy_src_init. Tries to apply the new configuration
  // Does not check for invalid MuBi or threshold alert values
  virtual task try_apply_base_configuration(entropy_src_dut_cfg newcfg, realtime pause,
                                            output bit completed);

    completed = 0;

    // Controls
    ral.entropy_control.es_type.set(newcfg.type_bypass);
    ral.entropy_control.es_route.set(newcfg.route_software);
    csr_update(.csr(ral.entropy_control));
    #(pause);

    ral.health_test_windows.fips_window.set(newcfg.fips_window_size);
    ral.health_test_windows.bypass_window.set(newcfg.bypass_window_size);
    csr_update(.csr(ral.health_test_windows));
    #(pause);

    // Thresholds for the continuous health checks:
    // REPCNT and REPCNTS

    if (!newcfg.default_ht_thresholds) begin
      ral.repcnt_thresholds.bypass_thresh.set(newcfg.repcnt_thresh_bypass);
      ral.repcnt_thresholds.fips_thresh.set(newcfg.repcnt_thresh_fips);
      csr_update(.csr(ral.repcnt_thresholds));

      ral.repcnts_thresholds.bypass_thresh.set(newcfg.repcnts_thresh_bypass);
      ral.repcnts_thresholds.fips_thresh.set(newcfg.repcnts_thresh_fips);
      csr_update(.csr(ral.repcnts_thresholds));
    end
    #(pause);

    // Windowed health test thresholds managed in derived vseq classes

    // FW_OV registers
    ral.fw_ov_control.fw_ov_mode.set(newcfg.fw_read_enable);
    ral.fw_ov_control.fw_ov_entropy_insert.set(newcfg.fw_over_enable);
    csr_update(.csr(ral.fw_ov_control));
    #(pause);

    ral.fw_ov_sha3_start.fw_ov_insert_start.set(newcfg.fw_ov_insert_start);
    csr_update(.csr(ral.fw_ov_sha3_start));
    #(pause);

    ral.alert_threshold.alert_threshold.set(newcfg.alert_threshold);
    ral.alert_threshold.alert_threshold_inv.set(newcfg.alert_threshold_inv);
    csr_update(.csr(ral.alert_threshold));
    #(pause);

    ral.observe_fifo_thresh.observe_fifo_thresh.set(newcfg.observe_fifo_thresh);
    csr_update(ral.observe_fifo_thresh);
    #(pause);

    ral.conf.fips_enable.set(newcfg.fips_enable);
    ral.conf.entropy_data_reg_enable.set(newcfg.entropy_data_reg_enable);
    ral.conf.fips_flag.set(newcfg.fips_flag);
    ral.conf.rng_fips.set(newcfg.rng_fips);
    ral.conf.rng_bit_enable.set(newcfg.rng_bit_enable);
    ral.conf.rng_bit_sel.set(newcfg.rng_bit_sel);
    ral.conf.threshold_scope.set(newcfg.ht_threshold_scope);
    csr_update(.csr(ral.conf));
    #(pause);

    // The CSR write accesses above may trigger recoverable alerts (e.g. in case invalid MuBis are
    // written to the CSRs). To handle such cases, the calling entropy_src_init() task listens for
    // recoverable alerts and if necessary aborts this task here. Because all this can take some
    // time, we must wait a couple of clock cycles before potentially locking configuration CSRs.
    // Otherwise, we may lock invalid configurations which would require resetting the DUT.
    wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(
        cfg.m_alert_agent_cfgs["recov_alert"].ping_delay_max +
        cfg.m_alert_agent_cfgs["recov_alert"].ack_delay_max +
        cfg.m_alert_agent_cfgs["recov_alert"].ack_stable_max +
        2); // Pause between back-to-back handshakes at sender end.

    // Register write enable lock is on be default
    // Setting this to zero will lock future writes
    csr_wr(.ptr(ral.sw_regupd), .value(newcfg.sw_regupd));
    #(pause);

    // Module_enables (should be done last)
    if (newcfg.module_enable == MuBi4True) begin
      // Use the enable method to invoke any callbacks.
      enable_dut();
    end else if (newcfg.module_enable == MuBi4False) begin
      disable_dut();
    end else begin
      // Explicitly write the invalid enable value
      // to the module_enable register.
      ral.module_enable.set(newcfg.module_enable);
      csr_update(.csr(ral.module_enable));
    end
    #(pause);

    ral.me_regwen.set(newcfg.me_regwen);
    csr_update(.csr(ral.me_regwen));
    #(pause);

    if (do_interrupt) begin
      ral.intr_enable.set(newcfg.en_intr);
      csr_update(ral.intr_enable);
    end

    cfg.clk_rst_vif.wait_clks(2);
    `uvm_info(`gfn, "Configuration Complete", UVM_MEDIUM)

    completed = 1;
  endtask

  // Setup basic entropy_src features, halting if a recoverable alert is detected
  //
  // If disable==1, explicitly clear module_enable before configuring
  // to remove the write_lock
  //
  // Outputs REGWEN = 0, if the device configuration was attempted when most registers
  // were locked. (Likely intentionally)
  virtual task entropy_src_init(entropy_src_dut_cfg newcfg=cfg.dut_cfg,
                                realtime pause=cfg.configuration_pause_time,
                                output bit completed,
                                output bit regwen);
    completed = 0;

    if (newcfg.preconfig_disable) begin
      disable_dut();
      `uvm_info(`gfn, "DUT Disabled", UVM_MEDIUM)
      if (ral.sw_regupd.sw_regupd.get()) begin
        `uvm_info(`gfn, "Waiting for REGWEN", UVM_HIGH)
        csr_spinwait(.ptr(ral.regwen.regwen), .exp_data(1));
        `uvm_info(`gfn, "REGWEN Detected", UVM_HIGH)
      end
    end

    csr_rd(.ptr(ral.regwen.regwen), .value(regwen));

    wait_no_outstanding_access();

    `uvm_info(`gfn, "Applying configuration", UVM_MEDIUM)

    `DV_SPINWAIT_EXIT(
      try_apply_base_configuration(newcfg, pause, completed);,
      while (!cfg.m_alert_agent_cfgs["recov_alert"].vif.is_alert_handshaking()) begin
         cfg.clk_rst_vif.wait_clks(1);
      end
      wait_no_outstanding_access();
    )

    if (!completed) begin
      bit [TL_DW - 1:0] value;
      `uvm_info(`gfn, "Detected recoverable alert", UVM_LOW)

      `uvm_info(`gfn, "Falling back on safe config", UVM_LOW)

      // Set all fields with redundancy to safe values
      entropy_src_safe_config();
      // Read the alert sts register, let the scoreboard validate the value (if enabled)
      csr_rd(.ptr(ral.recov_alert_sts), .value(value));
      `uvm_info(`gfn, $sformatf("RECOV_ALERT_STS (pre): %08x", value), UVM_MEDIUM)
      // clear the alert status register.
      csr_wr(.ptr(ral.recov_alert_sts), .value('h0));
      // Re-read the alert_status register to confirm that it has been cleared.
      csr_rd(.ptr(ral.recov_alert_sts), .value(value));
      `uvm_info(`gfn, $sformatf("RECOV_ALERT_STS: %08x", value), UVM_MEDIUM)
    end

    `uvm_info(`gfn, $sformatf("Exiting configuration, status %d", completed) , UVM_MEDIUM)

  endtask

  // helper task to clear any invalid configurations
  task entropy_src_safe_config();

    `uvm_info(`gfn, "Moving DUT into a safe configuration", UVM_MEDIUM)
    // explicitly clear module_enable to allow module writes
    disable_dut();

    // Clear all interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'hf));

    ral.entropy_control.es_type.set(MuBi4False);
    ral.entropy_control.es_route.set(MuBi4False);
    csr_update(.csr(ral.entropy_control));

    ral.conf.fips_enable.set(MuBi4False);
    ral.conf.entropy_data_reg_enable.set(MuBi4False);
    ral.conf.fips_flag.set(MuBi4False);
    ral.conf.rng_fips.set(MuBi4False);
    ral.conf.rng_bit_enable.set(MuBi4False);
    ral.conf.threshold_scope.set(MuBi4False);
    csr_update(.csr(ral.conf));

    ral.fw_ov_control.fw_ov_mode.set(MuBi4False);
    ral.fw_ov_control.fw_ov_entropy_insert.set(MuBi4False);
    csr_update(.csr(ral.fw_ov_control));

    ral.fw_ov_sha3_start.fw_ov_insert_start.set(MuBi4False);
    csr_update(.csr(ral.fw_ov_sha3_start));

    csr_wr(.ptr(ral.alert_threshold), .value(ral.alert_threshold.get_reset()));

    `uvm_info(`gfn, "Safe configuration", UVM_MEDIUM)

  endtask

  typedef enum int {
    TlSrcEntropyDataReg,
    TlSrcObserveFIFO
  } tl_data_source_e;

  // Poll the relevant interrupt bit for accessing either the ENTROPY_DATA or FW_OV_RD_DATA
  // register
  task poll(tl_data_source_e source = TlSrcEntropyDataReg, int spinwait_delay_ns = 0);

    uvm_reg_field intr_field;

    case (source)
      TlSrcEntropyDataReg: begin
        intr_field = ral.intr_state.es_entropy_valid;
      end
      TlSrcObserveFIFO: begin
        intr_field = ral.intr_state.es_observe_fifo_ready;
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid source for accessing TL entropy (environment error)")
      end
    endcase

    csr_spinwait(.ptr(intr_field), .exp_data(1'b1), .spinwait_delay_ns(spinwait_delay_ns));
  endtask


  // Read all data in ENTROPY_DATA or FW_OV_RD_DATA up to a certain amount
  //
  // Data is read in bundles, where the size of a bundle depends on the data
  // source.
  //
  // For the entropy_data register a bundle consists of CSRNG_BUS_WIDTH (=384) bits
  // and this it takes CSRNG_BUS_WIDTH/TL_DW (=12) reads to fetch a whole bundle.
  //
  // When accessing the observe FIFO via the FW_OV_RD_DATA register, the bundle size is TL_DW (=32)
  // bits.
  //
  // If max_bundles < 0, simply reads all available bundles.
  //
  // If source is TlSrcObserveFIFO and check_overflow is set to 1, this task checks whether
  // overflows occurred or not. This is done to make sure that the data read from the observe
  // FIFO is contiguous.
  task do_entropy_data_read(tl_data_source_e source = TlSrcEntropyDataReg,
                            int max_bundles = -1,
                            int timeout_ns = 250us / 1ns,
                            bit check_overflow = 0,
                            output int bundles_found);
    bit intr_status;
    bit done;
    bit read_max = 0;
    int num_words_to_read = 1;
    uvm_reg_field intr_field;
    uvm_reg       data_reg;

    bundles_found = 0;

    case (source)
      TlSrcEntropyDataReg: begin
        intr_field        = ral.intr_state.es_entropy_valid;
        data_reg          = ral.entropy_data;
      end
      TlSrcObserveFIFO: begin
        intr_field        = ral.intr_state.es_observe_fifo_ready;
        data_reg          = ral.fw_ov_rd_data;
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid source for accessing TL entropy (environment error)")
      end
    endcase

    `DV_SPINWAIT(
      do begin
        `uvm_info(`gfn, "READING INTERRUPT STS", UVM_DEBUG)
        csr_rd(.ptr(intr_field), .value(intr_status));
        if (intr_status) begin

          // How many words shall we read in one go?
          if (source == TlSrcEntropyDataReg) begin
            // The seed length (CSRNG_BUS_WIDTH) is an integer multiple of the bus width.
            num_words_to_read = entropy_src_pkg::CSRNG_BUS_WIDTH / TL_DW;
          end else begin
            // Check that the Observe FIFO hasn't overflown yet.
            // By checking for overflows before and after reading the observe FIFO we can make sure
            // that the data we are reading is contiguous.
            if (check_overflow) begin
              csr_rd_check(.ptr(ral.fw_ov_rd_fifo_overflow.fw_ov_rd_fifo_overflow),
                           .compare_value('0));
            end
            // Define how many words we're going to read from the Observe FIFO. For efficiency,
            // firmware will always read the maximum number of available words. But to reach
            // coverage and to have the FIFO overflow from time to time, we sometimes just read few
            // elements only.
            read_max = $urandom_range(0, 9) > 0;
            if (read_max) begin
              cfg.clk_rst_vif.wait_n_clks(2);
              num_words_to_read = `gmv(ral.observe_fifo_depth);
            end else begin
              csr_rd(.ptr(ral.observe_fifo_thresh), .value(num_words_to_read));
            end
            if ((max_bundles >= 0) && (num_words_to_read >= max_bundles)) begin
              num_words_to_read = max_bundles;
            end
          end

          do begin
            // Read and check the entropy.
            for (int i = 0; i < num_words_to_read; i++) begin
              bit [TL_DW-1:0] entropy_tlul;
              csr_rd(.ptr(data_reg), .value(entropy_tlul), .blocking(1'b1));
            end
            bundles_found += (source == TlSrcObserveFIFO ? num_words_to_read : 1);
            num_words_to_read = 0;

            // Check whether no overflow occurred while reading the observe FIFO and we are
            // still reading out contiguous data.
            if ((source == TlSrcObserveFIFO) && check_overflow) begin
              csr_rd_check(.ptr(ral.fw_ov_rd_fifo_overflow.fw_ov_rd_fifo_overflow),
                           .compare_value('0));
            end

            // Shall we continue reading more data?
            if (read_max) begin
              cfg.clk_rst_vif.wait_n_clks(2);
              num_words_to_read = `gmv(ral.observe_fifo_depth);
              if ((max_bundles >= 0) && (num_words_to_read >= max_bundles)) begin
                num_words_to_read = max_bundles;
              end
            end
            done = (max_bundles >= 0) && (bundles_found >= max_bundles);
          end while (num_words_to_read > 0 && !done);

          // Clear the appropriate interrupt bit
          `uvm_info(`gfn, "CLEARING FIFO INTERRUPT", UVM_DEBUG)
          csr_wr(.ptr(intr_field), .value(1'b1), .blocking(1'b1));
        end
      end while (intr_status && !done);, // do begin
    $sformatf("Timeout encountered while reading %s", source.name()), timeout_ns)
  endtask

  task run_rng_host_seq(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq);
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      rng_val = i % (2**`RNG_BUS_WIDTH);
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
  endtask // run_rng_host_seq

  task repcnt_ht_fail_seq(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                          int num_trans = m_rng_push_seq.num_trans);
    bit fail_symbol;
    int unsigned lane_idx;
    rng_val_t fixed_rng_val;
    // Shall we fail a single lane or the full symbol?
    fail_symbol = $urandom_range(0, 1);
    // Randomly select a lane to fail.
    lane_idx = $urandom_range(0, `RNG_BUS_WIDTH-1);
    // Set rng_val
    fixed_rng_val = rng_val_t'($urandom_range(0, 2**`RNG_BUS_WIDTH-1));
    for (int i = 0; i < num_trans; i++) begin
      if (fail_symbol) begin
        cfg.m_rng_agent_cfg.add_h_user_data(fixed_rng_val);
      end else begin
        rng_val = rng_val_t'($urandom_range(0, 2**`RNG_BUS_WIDTH-1));
        rng_val[lane_idx] = fixed_rng_val[lane_idx];
        cfg.m_rng_agent_cfg.add_h_user_data(fixed_rng_val);
      end
    end
  endtask // repcnt_ht_fail_seq

  task adaptp_ht_fail_seq(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                          bit[15:0] fips_lo_thresh, bit[15:0] fips_hi_thresh,
                          bit[15:0] bypass_lo_thresh, bit[15:0] bypass_hi_thresh,
                          int num_trans = m_rng_push_seq.num_trans);
    int unsigned lane_idx;
    ral.adaptp_hi_thresholds.fips_thresh.set(fips_hi_thresh);
    ral.adaptp_hi_thresholds.bypass_thresh.set(bypass_hi_thresh);
    csr_update(.csr(ral.adaptp_hi_thresholds));
    ral.adaptp_lo_thresholds.fips_thresh.set(fips_lo_thresh);
    ral.adaptp_lo_thresholds.bypass_thresh.set(bypass_lo_thresh);
    csr_update(.csr(ral.adaptp_lo_thresholds));
    // Turn on module_enable
    enable_dut();
    // Randomly select a lane to fail.
    lane_idx = $urandom_range(0, `RNG_BUS_WIDTH-1);
    // Set rng_val
    for (int i = 0; i < num_trans; i++) begin
      rng_val = rng_val_t'($urandom_range(0, 2**`RNG_BUS_WIDTH-1));
      rng_val[lane_idx] = (i % 16 == 0 ? (cfg.which_ht == high_test ? 0 : 1) :
                                         (cfg.which_ht == high_test ? 1 : 0));
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
  endtask // adaptp_ht_fail_seq

  task bucket_ht_fail_seq(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                          bit[15:0] fips_thresh, bit[15:0] bypass_thresh,
                          int num_trans = m_rng_push_seq.num_trans);
    parameter int BucketHtDataWidth = entropy_src_pkg::bucket_ht_data_width(`RNG_BUS_WIDTH);
    parameter int unsigned NumBucketHtInst = entropy_src_pkg::num_bucket_ht_inst(`RNG_BUS_WIDTH);
    int unsigned group_idx;
    ral.bucket_thresholds.fips_thresh.set(fips_thresh);
    ral.bucket_thresholds.bypass_thresh.set(bypass_thresh);
    csr_update(.csr(ral.bucket_thresholds));
    // Turn on module_enable
    enable_dut();
    // Randomly select a group to fail.
    group_idx = $urandom_range(0, NumBucketHtInst-1);
    // Set rng_val
    for (int i = 0; i < num_trans; i++) begin
      rng_val = rng_val_t'($urandom_range(0, 2**`RNG_BUS_WIDTH-1));
      rng_val[group_idx * BucketHtDataWidth +: BucketHtDataWidth - 1] = (i % 2 == 0 ? 5 : 10);
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
  endtask // bucket_ht_fail_seq

  task markov_ht_fail_seq(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                          bit[15:0] fips_lo_thresh, bit[15:0] fips_hi_thresh,
                          bit[15:0] bypass_lo_thresh, bit[15:0] bypass_hi_thresh,
                          int num_trans = m_rng_push_seq.num_trans);
    int unsigned lane_idx;
    ral.markov_hi_thresholds.fips_thresh.set(fips_hi_thresh);
    ral.markov_hi_thresholds.bypass_thresh.set(bypass_hi_thresh);
    csr_update(.csr(ral.markov_hi_thresholds));
    ral.markov_lo_thresholds.fips_thresh.set(fips_lo_thresh);
    ral.markov_lo_thresholds.bypass_thresh.set(bypass_lo_thresh);
    csr_update(.csr(ral.markov_lo_thresholds));
    // Turn on module_enable
    enable_dut();
    // Randomly select a lane to fail.
    lane_idx = $urandom_range(0, `RNG_BUS_WIDTH-1);
    // Set rng_val
    for (int i = 0; i < num_trans; i++) begin
      rng_val = rng_val_t'($urandom_range(0, 2**`RNG_BUS_WIDTH-1));
      rng_val[lane_idx] = (i % 2 == 0 ? (cfg.which_ht == high_test ? 0 : 1) :
                                        (cfg.which_ht == high_test ? 1 : 0));
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
  endtask // markov_ht_fail_seq

  task force_fifo_err(string path1, string path2, bit value1, bit value2,
                      uvm_reg_field reg_field, bit exp_data);
    if (!uvm_hdl_check_path(path1)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path1, value1));
    end
    if (!uvm_hdl_check_path(path2)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path2, value2));
    end
    cfg.clk_rst_vif.wait_clks(50);
    // Check register value
    csr_spinwait(.ptr(reg_field), .exp_data(exp_data));
    `DV_CHECK(uvm_hdl_release(path1));
    `DV_CHECK(uvm_hdl_release(path2));
  endtask // force_fifo_err

  task force_fifo_err_exception(string paths [4], bit values [4],
                                uvm_reg_field reg_field, bit exp_data);
    string data_path = "tb.dut.u_entropy_src_core.sfifo_esrng_rdata";
    foreach (paths[i]) begin
      if (!uvm_hdl_check_path(paths[i])) begin
        `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
      end else begin
        `DV_CHECK(uvm_hdl_force(paths[i], values[i]));
      end
    end
    if (!uvm_hdl_check_path(data_path)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(data_path, '0));
    end
    cfg.clk_rst_vif.wait_clks(50);
    // Check register value
    csr_spinwait(.ptr(reg_field), .exp_data(exp_data));
    foreach (paths[i]) begin
      `DV_CHECK(uvm_hdl_release(paths[i]));
    end
  endtask // force_fifo_err_exception

  task force_path_err(string path, bit [15:0] value, uvm_reg_field reg_field, bit exp_data);
    if (!uvm_hdl_check_path(path)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path, value));
      cfg.clk_rst_vif.wait_clks(50);
      `DV_CHECK(uvm_hdl_release(path));
      cfg.clk_rst_vif.wait_clks(50);
      // Check err_code register
      csr_rd_check(.ptr(reg_field), .compare_value(exp_data));
    end
  endtask // force_path_err

  task window_cntr_err_test(uvm_reg_field reg_field);
    string path = cfg.entropy_src_path_vif.cntr_err_path("window", cfg.which_cntr_replicate);
    `DV_CHECK_STD_RANDOMIZE_FATAL(path_err_val)
    // Force the path (cnt_q[1]) to stuck at a different value from cnt_q[0] to trigger
    // the counter error
    force_path_err(path, path_err_val, reg_field, 1'b1);
  endtask // window_cntr_err_test

  task repcnt_ht_cntr_test(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                           uvm_reg_field reg_field);
    string path;
    `DV_CHECK_STD_RANDOMIZE_FATAL(path_err_val)
    // Set a low threshold to introduce ht fails
    ral.repcnt_thresholds.fips_thresh.set(16'h0008);
    ral.repcnt_thresholds.bypass_thresh.set(16'h0008);
    csr_update(.csr(ral.repcnt_thresholds));
    repcnt_ht_fail_seq(m_rng_push_seq);
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
    cfg.clk_rst_vif.wait_clks(100);
    // Force repcnt ht counter err
    path = cfg.entropy_src_path_vif.cntr_err_path("repcnt_ht", cfg.which_cntr_replicate);
    // Force the path (cnt_q[1]) to stuck at a different value from cnt_q[0] to trigger
    // the counter error
    force_path_err(path, path_err_val, reg_field, 1'b1);
    // Write the threshold back to a high value
    ral.repcnt_thresholds.fips_thresh.set(16'hfffe);
    ral.repcnt_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.repcnt_thresholds));
  endtask // repcnt_ht_cntr_test

  task repcnts_ht_cntr_test(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                            uvm_reg_field reg_field);
    string path;
    `DV_CHECK_STD_RANDOMIZE_FATAL(path_err_val)
    // Set a low threshold to introduce ht fails
    ral.repcnts_thresholds.fips_thresh.set(16'h0008);
    ral.repcnts_thresholds.bypass_thresh.set(16'h0008);
    csr_update(.csr(ral.repcnts_thresholds));
    repcnt_ht_fail_seq(m_rng_push_seq);
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
    cfg.clk_rst_vif.wait_clks(100);
    // Force repcnts ht counter err
    path = cfg.entropy_src_path_vif.cntr_err_path("repcnts_ht", cfg.which_cntr_replicate);
    // Force the path (cnt_q[1]) to stuck at a different value from cnt_q[0] to trigger
    // the counter error
    force_path_err(path, path_err_val, reg_field, 1'b1);
    // Write the threshold back to a high value
    ral.repcnts_thresholds.fips_thresh.set(16'hfffe);
    ral.repcnts_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.repcnts_thresholds));
  endtask // repcnts_ht_cntr_test

  task adaptp_ht_cntr_test(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                           uvm_reg_field reg_field);
    string path;
    bit [15:0] fips_thresh = 16'h0008;
    bit [15:0] bypass_thresh = 16'h0008;
    `DV_CHECK_STD_RANDOMIZE_FATAL(path_err_val)
    adaptp_ht_fail_seq(m_rng_push_seq, fips_thresh, fips_thresh, bypass_thresh, bypass_thresh);
    // Start the sequence
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
    cfg.clk_rst_vif.wait_clks(100);
    // Force adaptp ht counter err
    path = cfg.entropy_src_path_vif.cntr_err_path("adaptp_ht", cfg.which_cntr_replicate);
    // Force the path (cnt_q[1]) to stuck at a different value from cnt_q[0] to trigger
    // the counter error
    force_path_err(path, path_err_val, reg_field, 1'b1);
    // Write the threshold back to a high value
    ral.adaptp_hi_thresholds.fips_thresh.set(16'hfffe);
    ral.adaptp_hi_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.adaptp_hi_thresholds));
    ral.adaptp_lo_thresholds.fips_thresh.set(16'hfffe);
    ral.adaptp_lo_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.adaptp_lo_thresholds));
  endtask // adaptp_ht_cntr_test

  task bucket_ht_cntr_test(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                           uvm_reg_field reg_field);
    string path;
    bit [15:0] fips_thresh = 16'h0008;
    bit [15:0] bypass_thresh = 16'h0008;
    `DV_CHECK_STD_RANDOMIZE_FATAL(path_err_val)
    fips_thresh = 16'h0008;
    bypass_thresh = 16'h0008;
    bucket_ht_fail_seq(m_rng_push_seq, fips_thresh, bypass_thresh);
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
    cfg.clk_rst_vif.wait_clks(100);
    // Force bucket ht counter err
    path = cfg.entropy_src_path_vif.cntr_err_path("bucket_ht", cfg.which_bin, cfg.which_ht_inst);
    // Force the path (cnt_q[1]) to stuck at a different value from cnt_q[0] to trigger
    // the counter error
    force_path_err(path, path_err_val, reg_field, 1'b1);
    // Write the threshold back to a high value
    ral.bucket_thresholds.fips_thresh.set(16'hfffe);
    ral.bucket_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.bucket_thresholds));
  endtask // bucket_ht_cntr_test

  task markov_ht_cntr_test(push_pull_host_seq#(`RNG_BUS_WIDTH) m_rng_push_seq,
                           uvm_reg_field reg_field);
    string path;
    bit [15:0] fips_thresh = 16'h0008;
    bit [15:0] bypass_thresh = 16'h0008;
    `DV_CHECK_STD_RANDOMIZE_FATAL(path_err_val)

    fips_thresh = 16'h0008;
    bypass_thresh = 16'h0008;
    markov_ht_fail_seq(m_rng_push_seq, fips_thresh, fips_thresh, bypass_thresh, bypass_thresh);
    // Start the sequence
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
    cfg.clk_rst_vif.wait_clks(100);
    // Force markov ht counter err
    path = cfg.entropy_src_path_vif.cntr_err_path("markov_ht", cfg.which_cntr_replicate);
    // Force the path (cnt_q[1]) to stuck at a different value from cnt_q[0] to trigger
    // the counter error
    force_path_err(path, path_err_val, reg_field, 1'b1);
    // Write the threshold back to a high value
    ral.markov_hi_thresholds.fips_thresh.set(16'hfffe);
    ral.markov_hi_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.markov_hi_thresholds));
    ral.markov_lo_thresholds.fips_thresh.set(16'hfffe);
    ral.markov_lo_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.markov_lo_thresholds));
  endtask // markov_ht_cntr_test

  // Find the first or last index in the original string that the target character appears
  function automatic int find_index (string target, string original_str, string which_index);
    int        index;
    case (which_index)
      "first": begin
        for (int i = original_str.len(); i > 0; i--) begin
          if (original_str[i] == target) index = i;
        end
      end
      "last": begin
        for (int i = 0; i < original_str.len(); i++) begin
          if (original_str[i] == target) index = i;
        end
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid index!")
      end
    endcase // case (which_index)
    return index;
  endfunction // find_index
endclass : entropy_src_base_vseq
