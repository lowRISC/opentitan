// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_stress_all_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_stress_all_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                              = 1;
    cfg.dut_cfg.fips_window_size            = 2048;
    cfg.dut_cfg.bypass_window_size          = 384;
    cfg.seed_cnt                            = 1;
    cfg.dut_cfg.route_software_pct          = 100;
    cfg.dut_cfg.entropy_data_reg_enable_pct = 100;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_stress_all_test
