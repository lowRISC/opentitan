// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rng_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual rng_if vif;

  entropy_type_t   entropy_type = RAND;
  uint             entropy_hold_clks, entropy_ok_delay_clks;

  `uvm_object_utils_begin(rng_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

endclass
