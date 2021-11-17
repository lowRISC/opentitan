// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_alert_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_alert_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                      = 0;
    cfg.use_invalid_mubi            = 1;
    cfg.route_software_pct          = 0;
    cfg.entropy_data_reg_enable_pct = 100;
    cfg.fw_read_pct                 = 100;
    cfg.fw_over_pct                 = 100;
    cfg.module_enable_pct           = 0;
    cfg.fips_enable_pct             = 100;
    cfg.sw_regupd_pct               = 100;
    cfg.type_bypass_pct             = 0;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_alert_test
