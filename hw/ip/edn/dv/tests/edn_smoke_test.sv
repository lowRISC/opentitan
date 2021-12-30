// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_smoke_test extends edn_base_test;

  `uvm_component_utils(edn_smoke_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    cfg.num_endpoints    = MIN_NUM_ENDPOINTS;
    cfg.use_invalid_mubi = 0;

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_HIGH)
  endfunction
endclass : edn_smoke_test
