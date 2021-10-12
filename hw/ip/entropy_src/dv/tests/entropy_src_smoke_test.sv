// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_smoke_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_smoke_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    // TODO: Enable scoreboard
    cfg.en_scb                      = 0;
    cfg.route_software_pct          = 100;
    cfg.entropy_data_reg_enable_pct = 100;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_smoke_test
