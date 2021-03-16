// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_rng_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_rng_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.enable_lfsr_pct    = 0;
    cfg.enable_ptrng_pct   = 100;
    cfg.route_software_pct = 100;
    cfg.type_bypass_pct    = 100;

    // TODO: Modify cfg_knob randomization to include lfsr/hardware

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_rng_test
