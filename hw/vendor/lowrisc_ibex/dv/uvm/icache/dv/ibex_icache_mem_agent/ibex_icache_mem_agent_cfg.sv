// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_mem_agent_cfg extends dv_base_agent_cfg;

  // Knobs
  bit          disable_pmp_errs = 0;
  bit          disable_mem_errs = 0;
  int unsigned mem_err_shift = 3;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual ibex_icache_mem_if vif;

  `uvm_object_param_utils_begin(ibex_icache_mem_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

endclass
