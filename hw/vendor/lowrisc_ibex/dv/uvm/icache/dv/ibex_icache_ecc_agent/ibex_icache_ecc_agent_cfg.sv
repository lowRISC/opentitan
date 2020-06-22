// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_ecc_agent_cfg extends dv_base_agent_cfg;

  // Knobs
  bit          error_prob_pc = 10;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual ibex_icache_ecc_if vif;

  `uvm_object_utils_begin(ibex_icache_ecc_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

endclass
