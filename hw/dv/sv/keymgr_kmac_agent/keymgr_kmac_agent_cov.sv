// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_agent_cov extends dv_base_agent_cov #(keymgr_kmac_agent_cfg);
  `uvm_component_utils(keymgr_kmac_agent_cov)

  // covergroups

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // instantiate all covergroups here
  endfunction : new

endclass
