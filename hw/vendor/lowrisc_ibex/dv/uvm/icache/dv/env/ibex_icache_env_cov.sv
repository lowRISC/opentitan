// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class ibex_icache_env_cov extends dv_base_env_cov #(.CFG_T (ibex_icache_env_cfg));

  `uvm_component_utils(ibex_icache_env_cov)

  // the base class provides the following handles for use:
  // ibex_icache_env_cfg: cfg

  // covergroups
  // [add covergroups here]

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // [instantiate covergroups here]
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
  endfunction

endclass
