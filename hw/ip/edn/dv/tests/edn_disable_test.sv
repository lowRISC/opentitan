// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_disable_test extends edn_base_test;

  `uvm_component_utils(edn_disable_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.boot_req_mode_pct = 100;
    cfg.auto_req_mode_pct = 0;
    cfg.min_num_boot_reqs = 1;
    cfg.max_num_boot_reqs = 4;
    cfg.min_num_ep_reqs   = 4;
    cfg.max_num_ep_reqs   = 4;
    cfg.force_disable_pct = 100;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    cfg.num_endpoints = 1;

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_HIGH)
  endfunction
endclass : edn_disable_test
