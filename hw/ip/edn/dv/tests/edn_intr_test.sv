// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_intr_test extends edn_base_test;

  `uvm_component_utils(edn_intr_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb            = 0;
    cfg.use_invalid_mubi  = 0;

    // TODO(#18971): This test is currently not run when EDN is in Auto mode or in Boot mode (i.e.,
    // only in SW mode), because `auto_req_mode_pct` and `boot_req_mode_pct` have a value of `0` by
    // inheritance.  The fatal error interrupt should also be triggered and verified in Auto mode
    // and in Boot mode, though; but this is currently not supported by `edn_intr_vseq`.  When this
    // is resolved, `edn_intr_test` can potentially be merged with `edn_err_test`, because their
    // only difference currently is the value of `auto_req_mode_pct` and `boot_req_mode_pct`.

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : edn_intr_test
