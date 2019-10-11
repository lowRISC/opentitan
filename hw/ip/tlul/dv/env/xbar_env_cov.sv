// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class xbar_env_cov extends dv_base_env_cov #(.CFG_T(xbar_env_cfg));
  `uvm_component_utils(xbar_env_cov)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass
