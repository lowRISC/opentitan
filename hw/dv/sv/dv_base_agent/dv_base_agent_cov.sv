// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A generic coverage component for an agent. An instance of some subclass will be instantiated in
// as the coverage object in the agent's monitor.

class dv_base_agent_cov #(type CFG_T = dv_base_agent_cfg) extends uvm_component;
  `uvm_component_param_utils(dv_base_agent_cov #(CFG_T))

  CFG_T cfg;

  extern function new (string name="", uvm_component parent=null);
endclass

function dv_base_agent_cov::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction
