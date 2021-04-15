// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_smoke_test extends edn_base_test;

  `uvm_component_utils(edn_smoke_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.auto_req_mode_pct = 0;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : edn_smoke_test
