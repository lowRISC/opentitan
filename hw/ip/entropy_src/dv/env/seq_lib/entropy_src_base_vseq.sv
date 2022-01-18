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

  rand bit [3:0]   rng_val;

  // various knobs to enable certain routines
  bit  do_entropy_src_init = 1'b1;

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

    csr_rd(.ptr( ral.repcnt_hi_watermarks), .value(val));
    csr_rd(.ptr(ral.repcnts_hi_watermarks), .value(val));
    csr_rd(.ptr( ral.adaptp_hi_watermarks), .value(val));
    csr_rd(.ptr( ral.adaptp_lo_watermarks), .value(val));
    csr_rd(.ptr(  ral.extht_hi_watermarks), .value(val));
    csr_rd(.ptr(  ral.extht_lo_watermarks), .value(val));
    csr_rd(.ptr( ral.bucket_hi_watermarks), .value(val));
    csr_rd(.ptr( ral.markov_hi_watermarks), .value(val));
    csr_rd(.ptr( ral.markov_lo_watermarks), .value(val));

    csr_rd(.ptr(   ral.repcnt_total_fails), .value(val));
    csr_rd(.ptr(  ral.repcnts_total_fails), .value(val));
    csr_rd(.ptr(ral.adaptp_hi_total_fails), .value(val));
    csr_rd(.ptr(ral.adaptp_lo_total_fails), .value(val));
    csr_rd(.ptr( ral.extht_hi_total_fails), .value(val));
    csr_rd(.ptr( ral.extht_lo_total_fails), .value(val));
    csr_rd(.ptr(   ral.bucket_total_fails), .value(val));
    csr_rd(.ptr(ral.markov_hi_total_fails), .value(val));
    csr_rd(.ptr(ral.markov_lo_total_fails), .value(val));

    csr_rd(.ptr(    ral.alert_fail_counts), .value(val));
    csr_rd(.ptr(    ral.extht_fail_counts), .value(val));
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "CSRNG_ONLY") begin
      cfg.csrng_rst_vif.apply_reset();
    end else begin
      super.apply_reset(kind);
    end
  endtask

  virtual task dut_shutdown();
    bit seeds_found;
    // check for pending entropy_src operations and wait for them to complete
    `uvm_info(`gfn, "Shutting down", UVM_LOW)
    do begin
      #( 1us);
      `uvm_info(`gfn, "Polling for remaining data (clear entropy_data interrupt)", UVM_LOW)
      do_entropy_data_read(-1, seeds_found);
      `uvm_info(`gfn, $sformatf("Found %01d seeds", seeds_found), UVM_HIGH)
    end while (seeds_found > 0);

    check_ht_diagnostics();

    super.dut_shutdown();
    // Special feature related to entropy_src virtual sequences:
    // We notify the environment that we are complete.
    apply_reset("CSRNG_ONLY");
  endtask

  // setup basic entropy_src features
  virtual task entropy_src_init();
    // Fuses
    cfg.otp_en_es_fw_read_vif.drive(.val(cfg.otp_en_es_fw_read));
    cfg.otp_en_es_fw_over_vif.drive(.val(cfg.otp_en_es_fw_over));

    // Register write enable
    // TODO Do we need to check main_sm_idle before writing DUT registers?
    csr_wr(.ptr(ral.regwen), .value(cfg.regwen));

    // Controls
    ral.entropy_control.es_type.set(cfg.type_bypass);
    ral.entropy_control.es_route.set(cfg.route_software);
    csr_update(.csr(ral.entropy_control));

    // Enables
    ral.conf.enable.set(cfg.enable);
    ral.conf.entropy_data_reg_enable.set(cfg.entropy_data_reg_enable);
    ral.conf.boot_bypass_disable.set(cfg.boot_bypass_disable);
    ral.conf.rng_bit_enable.set(cfg.rng_bit_enable);
    ral.conf.rng_bit_sel.set(cfg.rng_bit_sel);
    csr_update(.csr(ral.conf));

  endtask

  // Read all seeds in ENTROPY_DATA until
  // a. Max_tries seed have been read
  // b. The intr_state register indicates no more data in entropy_data
  //
  // If max_tries < 0, simply reads all available seeds.
  task do_entropy_data_read(int max_seeds = -1, output int seeds_found);
    bit intr_status;
    bit done;
    seeds_found = 0;

    do begin
      csr_rd(.ptr(ral.intr_state.es_entropy_valid), .value(intr_status));
      if (intr_status) begin
        // Read and check entropy
        for (int i = 0; i < entropy_src_pkg::CSRNG_BUS_WIDTH/TL_DW; i++) begin
          bit [TL_DW-1:0] entropy_tlul;
          csr_rd(.ptr(ral.entropy_data), .value(entropy_tlul));
        end
        // Clear entropy_valid interrupt bit
        csr_wr(.ptr(ral.intr_state.es_entropy_valid), .value(1'b1), .blocking(1'b1));
        seeds_found++;
      end
      done = (max_seeds >= 0) && (seeds_found >= max_seeds);
    end while (intr_status && !done);
  endtask

endclass : entropy_src_base_vseq
