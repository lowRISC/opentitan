// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Configuration class for rram_macro_agent

class rram_macro_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils(rram_macro_agent_cfg)

  virtual rram_macro_if m_vif;

  extern function new(string name="");
endclass

function rram_macro_agent_cfg::new(string name="");
  super.new(name);

  // This agent is only ever passive, so make that the default and don't request a driver.
  if_mode = dv_utils_pkg::Monitor;
  has_driver = 0;
endfunction
