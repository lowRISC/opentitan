// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_alert_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_alert_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                              = 1;
    cfg.dut_cfg.fips_enable_pct             = 100;
    cfg.dut_cfg.entropy_data_reg_enable_pct = 100;
    cfg.dut_cfg.rng_bit_enable_pct          = 0;
    cfg.dut_cfg.fw_read_pct                 = 0;
    cfg.dut_cfg.fw_over_pct                 = 0;
    cfg.dut_cfg.bad_mubi_cfg_pct            = 0;
    cfg.dut_cfg.route_software_pct          = 0;
    cfg.dut_cfg.module_enable_pct           = 0;
    cfg.dut_cfg.default_ht_thresholds_pct   = 100;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_alert_test
