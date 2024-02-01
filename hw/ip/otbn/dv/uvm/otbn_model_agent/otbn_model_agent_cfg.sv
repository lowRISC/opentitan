// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_model_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual otbn_model_if#(.ImemSizeByte(otbn_reg_pkg::OTBN_IMEM_SIZE)) vif;

  `uvm_object_utils_begin(otbn_model_agent_cfg)
  `uvm_object_utils_end

  function new (string name="");
    super.new(name);
    // This agent is always passive.
    this.is_active = 1'b0;
  endfunction : new

endclass
