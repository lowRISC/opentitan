// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Configuration class for rv_dm_mode_agent

class rv_dm_mode_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils(rv_dm_mode_agent_cfg)

  virtual rv_dm_mode_if vif;

  extern function new (string name="");
endclass

function rv_dm_mode_agent_cfg::new (string name="");
  super.new(name);
endfunction
