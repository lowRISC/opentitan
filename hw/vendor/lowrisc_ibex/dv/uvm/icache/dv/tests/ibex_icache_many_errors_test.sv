// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_many_errors_test extends ibex_icache_base_test;

  `uvm_component_utils(ibex_icache_many_errors_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Increase the error rate (to roughly 50%)
    cfg.mem_agent_cfg.mem_err_shift = 1;
  endfunction

endclass : ibex_icache_many_errors_test
