// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_agent_cov #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends dv_base_agent_cov #(key_sideload_agent_cfg#(KEY_T));
  `uvm_component_utils(key_sideload_agent_cov#(KEY_T))

  // the base class provides the following handles for use:
  // key_sideload_agent_cfg: cfg

  // covergroups

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // instantiate all covergroups here
  endfunction : new

endclass
