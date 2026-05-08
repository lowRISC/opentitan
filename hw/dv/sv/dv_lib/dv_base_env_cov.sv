// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base class for coverage collection. This base class only really contains the CFG_T handle, that
// points to the config for the environment in use.

class dv_base_env_cov #(type CFG_T = dv_base_env_cfg) extends uvm_component;
  `uvm_component_param_utils(dv_base_env_cov #(CFG_T))

  CFG_T cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
