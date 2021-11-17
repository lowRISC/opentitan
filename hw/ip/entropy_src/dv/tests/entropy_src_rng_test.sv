// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_rng_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_rng_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.rng_bit_enable_pct          = 0;

    cfg.en_scb                      = 1;
    cfg.fips_window_size            = 2048;
    cfg.bypass_window_size          = 384;
    cfg.boot_mode_retry_limit       = 10;
    cfg.entropy_data_reg_enable_pct = 100;
    cfg.sim_duration                = 100ms;
    cfg.hard_mtbf                   = 100s;
    cfg.soft_mtbf                   = 7500us;
    cfg.adaptp_sigma_min            = 1.0;
    cfg.adaptp_sigma_max            = 2.0;
    cfg.bucket_sigma_min            = 1.0;
    cfg.bucket_sigma_max            = 2.0;
    cfg.markov_sigma_min            = 1.0;
    cfg.markov_sigma_max            = 2.0;
    cfg.alert_max_delay             = 5;

    // Allow for software reads, but let the vseq body do the enabling
    cfg.route_software_pct          = 0;
    cfg.module_enable_pct           = 0;
    cfg.fips_enable_pct             = 100;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_rng_test
