// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_rng_max_rate_test extends entropy_src_rng_test;

  `uvm_component_utils(entropy_src_rng_max_rate_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    // RNG failures and CSR-driven alert events won't happen in this test.
    cfg.hard_mtbf                = -1;
    cfg.soft_mtbf                = -1;
    cfg.mean_rand_csr_alert_time = -1;
    // We are interested in reconfiguring the DUT frequently to try many configurations for
    // coverage. To this end, this test configures the RNG agent to produce entropy at the
    // highest possible rate. At this rate, the initial boot-time/non-FIPS seed is produced
    // after roughly 7us (rng_bit_enable = 0) or 30us (rng_bit_enable = 1) on average. The
    // first FIPS seed is then available after roughly 80us and further seeds after 40us
    // (rng_bit_enable = 0).
    cfg.mean_rand_reconfig_time = 500us;
    // This test automatically switches the DUT from non-FIPS to FIPS mode once a seed
    // is observed. However, as we reconfigure the DUT very frequently, this automatic
    // switch might not happen.
    cfg.dut_cfg.fips_enable_pct = 60;
    // We want to hit all rng_bit_enable settings (off, bit 0 - 3) w/ and w/o bypass and
    // fips_enable.
    cfg.dut_cfg.rng_bit_enable_pct = 80;
    cfg.dut_cfg.type_bypass_pct = 50;
    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_rng_max_rate_test
