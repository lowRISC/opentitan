// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent_cov extends dv_base_agent_cov #(i2c_agent_cfg);
  `uvm_component_utils(i2c_agent_cov)

  //TODO: instantiate all covergroups here
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass
