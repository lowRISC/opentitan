// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_env_cov extends cip_base_env_cov #(.CFG_T(${name}_env_cfg));
% else:
class ${name}_env_cov extends dv_base_env_cov #(.CFG_T(${name}_env_cfg));
% endif
  `uvm_component_utils(${name}_env_cov)

  // the base class provides the following handles for use:
  // ${name}_env_cfg: cfg

  // covergroups

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // instantiate all covergroups here
  endfunction : new

endclass
