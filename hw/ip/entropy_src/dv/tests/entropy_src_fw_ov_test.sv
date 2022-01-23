// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_fw_ov_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_fw_ov_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                      = 1;
    cfg.fips_window_size            = 2048;
    cfg.bypass_window_size          = 384;
    cfg.seed_cnt                    = 12;
    cfg.boot_mode_retry_limit       = 10;
    cfg.route_software_pct          = 0;
    cfg.fw_read_pct                 = 100;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_fw_ov_test
