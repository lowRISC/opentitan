// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_fw_ov_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_fw_ov_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                              = 1;
    cfg.alert_max_delay                     = 5;

    cfg.dut_cfg.boot_mode_retry_limit       = 10;
    cfg.sim_duration                        = 10ms;
    cfg.hard_mtbf                           = 100s;
    cfg.mean_rand_reconfig_time             = 1ms;
    cfg.mean_rand_csr_alert_time            = 2ms;
    cfg.soft_mtbf                           = 7500us;

    // Apply truly impossible standards, to confirm that HT's don't matter here
    cfg.dut_cfg.adaptp_sigma_min_typ        = 0.0;
    cfg.dut_cfg.adaptp_sigma_min_tight      = 0.0;
    cfg.dut_cfg.adaptp_sigma_max_typ        = 0.0;
    cfg.dut_cfg.adaptp_sigma_max_tight      = 0.0;
    cfg.dut_cfg.bucket_sigma_min_typ        = 0.0;
    cfg.dut_cfg.bucket_sigma_min_tight      = 0.0;
    cfg.dut_cfg.bucket_sigma_max_typ        = 0.0;
    cfg.dut_cfg.bucket_sigma_max_tight      = 0.0;
    cfg.dut_cfg.markov_sigma_min_typ        = 0.0;
    cfg.dut_cfg.markov_sigma_min_tight      = 0.0;
    cfg.dut_cfg.markov_sigma_max_typ        = 0.0;
    cfg.dut_cfg.markov_sigma_max_tight      = 0.0;

    cfg.dut_cfg.sw_regupd_pct               = 50;
    cfg.dut_cfg.preconfig_disable_pct       = 50;

    cfg.dut_cfg.entropy_data_reg_enable_pct = 50;
    cfg.dut_cfg.route_software_pct          = 50;
    cfg.otp_en_es_fw_read_pct               = 50;
    // Always allow FW override for this test
    cfg.otp_en_es_fw_over_pct               = 100;

    cfg.dut_cfg.ht_threshold_scope_pct      = 50;
    cfg.dut_cfg.default_ht_thresholds_pct   = 0;

    // Preferentially generate non-fips data, with the understanding that this test
    // will automatically switch the DUT from non-fips to fips mode once a seed
    // is observed, or else will otherwise reconfigure
    cfg.dut_cfg.fips_enable_pct             = 25;
    cfg.dut_cfg.type_bypass_pct             = 75;

    // Always read data from the Observe FIFO
    cfg.dut_cfg.fw_read_pct                 = 100;
    cfg.dut_cfg.fw_over_pct                 = 100;
    // Spurious injection parameter has no meaning here.
    cfg.spurious_inject_entropy_pct = 50;

    // RNG bit Enable shouldn't matter for this test. Randomize anyway
    cfg.dut_cfg.rng_bit_enable_pct          = 80;

    // TODO: Randomize@50%
    cfg.dut_cfg.fips_enable_pct             = 50;
    cfg.dut_cfg.module_enable_pct           = 100;
    cfg.induce_targeted_transition_pct      = 75;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_fw_ov_test
