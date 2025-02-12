// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class ac_range_check_env_cov extends cip_base_env_cov #(.CFG_T(ac_range_check_env_cfg));
  `uvm_component_utils(ac_range_check_env_cov)

  // The base class provides the following handles for use:
  // ac_range_check_env_cfg: cfg

  // Covergroups
  // TODO MVy [add covergroups here]

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // TODO MVy [instantiate covergroups here]
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO MVy [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
