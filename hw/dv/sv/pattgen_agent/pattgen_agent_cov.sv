// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_agent_cov extends dv_base_agent_cov #(pattgen_agent_cfg);
  `uvm_component_utils(pattgen_agent_cov)

  // the base class provides the following handles for use:
  // pattgen_agent_cfg: cfg
  // TODO: covergroups

  function new(string name, uvm_component parent);
    super.new(name, parent);
    //TODO:  instantiate all covergroups here
  endfunction : new

endclass
