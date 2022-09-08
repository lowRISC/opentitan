// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_alert_test extends edn_base_test;

  `uvm_component_utils(edn_alert_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb            = 0;
    cfg.enable_pct        = 100;
    cfg.boot_req_mode_pct = 0;
    cfg.cmd_fifo_rst_pct  = 100;
    cfg.use_invalid_mubi  = 1;
    cfg.num_endpoints     = MIN_NUM_ENDPOINTS;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : edn_alert_test
