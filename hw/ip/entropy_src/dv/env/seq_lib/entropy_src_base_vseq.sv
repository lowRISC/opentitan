// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_base_vseq extends cip_base_vseq #(
    .RAL_T               (entropy_src_reg_block),
    .CFG_T               (entropy_src_env_cfg),
    .COV_T               (entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T (entropy_src_virtual_sequencer)
  );
  `uvm_object_utils(entropy_src_base_vseq)

  rand bit [3:0]                     rng_val;
  rand bit [NumEntropySrcIntr - 1:0] en_intr;

  // various knobs to enable certain routines
  bit  do_entropy_src_init = 1'b1;
  bit  do_interrupt        = 1'b1;

  virtual entropy_src_cov_if   cov_vif;

  `uvm_object_new

  virtual task body();
    if (!uvm_config_db#(virtual entropy_src_cov_if)::get
        (null, "*.env" , "entropy_src_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get entropy_src_cov_if from uvm_config_db"))
    end

    cov_vif.cg_cfg_sample(.cfg(cfg));
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    cfg.otp_en_es_fw_read_vif.drive(.val(cfg.otp_en_es_fw_read));
    cfg.otp_en_es_fw_over_vif.drive(.val(cfg.otp_en_es_fw_over));

    super.dut_init();

    if (do_entropy_src_init) entropy_src_init();
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
        "repcnt_hi_watermarks", "repcnts_hi_watermarks", "adaptp_hi_watermarks",
        "adaptp_lo_watermarks", "extht_hi_watermarks", "extht_lo_watermarks",
        "bucket_hi_watermarks", "markov_hi_watermarks", "markov_lo_watermarks",
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
    end else begin
      super.apply_reset(kind);
    end
  endtask

  virtual task dut_shutdown();
    bit bundles_found;
    // check for pending entropy_src operations and wait for them to complete
    `uvm_info(`gfn, "Shutting down", UVM_LOW)
    do begin
      #( 1us);
      `uvm_info(`gfn, "Polling for remaining data (clear entropy_data interrupt)", UVM_LOW)
      do_entropy_data_read(.max_bundles(-1), .bundles_found(bundles_found));
      `uvm_info(`gfn, $sformatf("Found %01d seeds", bundles_found), UVM_HIGH)
    end while (bundles_found > 0);

    `uvm_info(`gfn, "Disabling DUT", UVM_MEDIUM)
    ral.module_enable.module_enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.module_enable));

    `uvm_info(`gfn, "Checking diagnostics", UVM_MEDIUM)
    check_ht_diagnostics();
    `uvm_info(`gfn, "Clearing Alerts", UVM_MEDIUM)
    ral.recov_alert_sts.es_main_sm_alert.set(1'b0);
    csr_update(.csr(ral.recov_alert_sts));
    super.dut_shutdown();
    apply_reset(.kind("CSRNG_ONLY"));
  endtask

  // setup basic entropy_src features
  virtual task entropy_src_init();
    // Controls
    ral.entropy_control.es_type.set(cfg.type_bypass);
    ral.entropy_control.es_route.set(cfg.route_software);
    csr_update(.csr(ral.entropy_control));

    // Thresholds managed in derived vseq classes

    // FW_OV registers
    ral.fw_ov_control.fw_ov_mode.set(cfg.fw_read_enable);
    ral.fw_ov_control.fw_ov_entropy_insert.set(cfg.fw_over_enable);
    csr_update(.csr(ral.fw_ov_control));

    ral.observe_fifo_thresh.observe_fifo_thresh.set(cfg.observe_fifo_thresh);
    csr_update(ral.observe_fifo_thresh);

    // Enables (should be done last)
    ral.conf.fips_enable.set(cfg.fips_enable);
    ral.conf.entropy_data_reg_enable.set(cfg.entropy_data_reg_enable);
    ral.conf.rng_bit_enable.set(cfg.rng_bit_enable);
    ral.conf.rng_bit_sel.set(cfg.rng_bit_sel);
    ral.conf.threshold_scope.set(cfg.ht_threshold_scope);
    csr_update(.csr(ral.conf));

    // Register write enable lock is on be default
    // Setting this to zero will lock future writes
    csr_wr(.ptr(ral.sw_regupd), .value(cfg.sw_regupd));

    // Module_enables (should be done last)
    ral.module_enable.set(cfg.module_enable);
    csr_update(.csr(ral.module_enable));

    ral.me_regwen.set(cfg.me_regwen);
    csr_update(.csr(ral.me_regwen));

    if (do_interrupt) begin
      ral.intr_enable.set(en_intr);
      csr_update(ral.intr_enable);
    end


  endtask

  typedef enum int {
    TlSrcEntropyDataReg,
    TlSrcObserveFIFO
  } tl_data_source_e;

  // Poll the relevant interrupt bit for accessing either the ENTROPY_DATA or FW_OV_RD_DATA
  // register
  task poll(tl_data_source_e source = TlSrcEntropyDataReg);

    uvm_reg_field intr_field;

    case (source)
      TlSrcEntropyDataReg: begin
        intr_field = ral.intr_state.es_entropy_valid;
      end
      TlSrcObserveFIFO: begin
        intr_field = ral.intr_state.es_observe_fifo_ready;
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid source for accessing TL entropy (enviroment error)")
      end
    endcase

    csr_spinwait(.ptr(intr_field), .exp_data(1'b1));
  endtask


  // Read all data in ENTROPY_DATA or FW_OV_RD_DATA up to a certain ammount
  //
  // Data is read in bundles, where the size of a bundle depends on the data
  // source.
  //
  // For the entropy_data register a bundle consists of CSRNG_BUS_WIDTH (=384) bits
  // and this it takes CSRNG_BUS_WIDTH/TL_DW (=12) reads to fetch a whole bundle.
  //
  // When accessing the observe_fifo via the FW_OV_RD_DATA register the bundle size is
  // programmable and set to be equal to the value set in the OBSERVE_FIFO_DEPTH register
  // (TODO: What happens if the depth is zero?)
  //
  // a. max_bundles bundles have been read
  // b. The intr_state register indicates no more data in entropy_data
  //
  // If max_tries < 0, simply reads all available bundles.
  task do_entropy_data_read(tl_data_source_e source = TlSrcEntropyDataReg,
                            int max_bundles = -1,
                            output int bundles_found);
    bit intr_status;
    bit done;
    int cnt_per_interrupt;

    uvm_reg_field intr_field;
    uvm_reg       data_reg;

    bundles_found = 0;

    case (source)
      TlSrcEntropyDataReg: begin
        intr_field        = ral.intr_state.es_entropy_valid;
        data_reg          = ral.entropy_data;
        cnt_per_interrupt = entropy_src_pkg::CSRNG_BUS_WIDTH / TL_DW;
      end
      TlSrcObserveFIFO: begin
        intr_field        = ral.intr_state.es_observe_fifo_ready;
        data_reg          = ral.fw_ov_rd_data;
        cnt_per_interrupt = ral.observe_fifo_thresh.get();
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid source for accessing TL entropy (enviroment error)")
      end
    endcase

    do begin
      csr_rd(.ptr(intr_field), .value(intr_status));
      if (intr_status) begin
        // Read and check entropy
        for (int i = 0; i < cnt_per_interrupt; i++) begin
          bit [TL_DW-1:0] entropy_tlul;
          csr_rd(.ptr(data_reg), .value(entropy_tlul));
        end
        // Clear the appropriate interrupt bit
        csr_wr(.ptr(intr_field), .value(1'b1), .blocking(1'b1));
        bundles_found++;
      end
      done = (max_bundles >= 0) && (bundles_found >= max_bundles);
    end while (intr_status && !done);
  endtask

endclass : entropy_src_base_vseq
