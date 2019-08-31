// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_agent_cov #(type CFG_T = dv_base_agent_cfg) extends uvm_component;
  `uvm_component_param_utils(dv_base_agent_cov #(CFG_T))

  CFG_T cfg;

  `uvm_component_new

endclass
