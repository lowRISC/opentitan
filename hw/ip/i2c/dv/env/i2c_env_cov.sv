// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_env_cov extends cip_base_env_cov#(
    .CFG_T(i2c_env_cfg)
);
  `uvm_component_utils(i2c_env_cov)

  // TODO: instantiate all covergroups here
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass
