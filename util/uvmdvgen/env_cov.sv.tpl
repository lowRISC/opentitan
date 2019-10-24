// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

% if is_cip:
class ${name}_env_cov extends cip_base_env_cov #(.CFG_T(${name}_env_cfg));
% else:
class ${name}_env_cov extends dv_base_env_cov #(.CFG_T(${name}_env_cfg));
% endif
  `uvm_component_utils(${name}_env_cov)

  // the base class provides the following handles for use:
  // ${name}_env_cfg: cfg

  // covergroups
  // [add covergroups here]

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // [instantiate covergroups here]
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
% if is_cip:
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
% endif
  endfunction

endclass
