// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_rng_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_rng_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                      = 1;
    cfg.alert_max_delay             = 5;
    cfg.rng_ignores_backpressure    = 1;

    cfg.sim_duration                = 10ms;
    cfg.hard_mtbf                   = 3ms;
    cfg.mean_rand_reconfig_time     = 3ms;
    // The random alerts only need to happen frequently enough to
    // close coverage
    cfg.mean_rand_csr_alert_time    = 20ms;
    // The following should be enough to confirm that OTP-silenced configurations are not
    // outputting any seeds.
    // TODO (V3/Enhancement): Add coverpoints (with sampling ifs) and assertions to
    // confirm that data is actually being dropped in the DUT. (Silent configs are not counted
    // by existing CP's as we only sample when seeds are generated)
    cfg.max_silent_reconfig_time    = 100us;
    cfg.soft_mtbf                   = 7500us;

    // Apply standards ranging from strict to relaxed
    cfg.dut_cfg.adaptp_sigma_min_tight      = 0.5;
    cfg.dut_cfg.adaptp_sigma_max_tight      = 2.0;
    cfg.dut_cfg.adaptp_sigma_min_typ        = 3.0;
    cfg.dut_cfg.adaptp_sigma_max_typ        = 6.0;

    cfg.dut_cfg.bucket_sigma_min_tight      = 0.5;
    cfg.dut_cfg.bucket_sigma_max_tight      = 2.0;
    cfg.dut_cfg.bucket_sigma_min_typ        = 3.0;
    cfg.dut_cfg.bucket_sigma_max_typ        = 6.0;

    cfg.dut_cfg.markov_sigma_min_tight      = 0.5;
    cfg.dut_cfg.markov_sigma_max_tight      = 2.0;
    cfg.dut_cfg.markov_sigma_min_typ        = 3.0;
    cfg.dut_cfg.markov_sigma_max_typ        = 6.0;

    cfg.dut_cfg.sw_regupd_pct               = 50;
    cfg.dut_cfg.preconfig_disable_pct       = 50;

    cfg.dut_cfg.entropy_data_reg_enable_pct = 50;
    cfg.dut_cfg.route_software_pct          = 50;
    cfg.otp_en_es_fw_read_pct               = 33;
    cfg.otp_en_es_fw_read_inval_pct         = 33;
    cfg.otp_en_es_fw_over_pct               = 33;
    cfg.otp_en_es_fw_over_inval_pct         = 33;

    cfg.dut_cfg.ht_threshold_scope_pct      = 50;
    cfg.dut_cfg.default_ht_thresholds_pct   = 0;

    // Preferentially generate non-fips data, with the understanding that this test
    // will automatically switch the DUT from non-fips to fips mode once a seed
    // is observed, or else will otherwise reconfigure
    cfg.dut_cfg.fips_enable_pct             = 25;
    cfg.dut_cfg.type_bypass_pct             = 75;

    // Sometimes read data from the Observe FIFO (but almost always take entropy from RNG)
    cfg.dut_cfg.fw_read_pct                 = 50;
    cfg.dut_cfg.fw_over_pct                 = 10;
    // Sometimes inject data, even if not configured
    cfg.spurious_inject_entropy_pct = 50;

    cfg.dut_cfg.rng_bit_enable_pct          = 80;

    cfg.dut_cfg.module_enable_pct           = 0;
    cfg.dut_cfg.bad_mubi_cfg_pct            = 50;
    cfg.dut_cfg.tight_thresholds_pct        = 50;
    cfg.induce_targeted_transition_pct      = 75;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_rng_test
