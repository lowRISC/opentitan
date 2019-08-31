// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Core ibex environment configuration class
// ---------------------------------------------
class core_ibex_env_cfg extends uvm_object;

  rand tl_agent_cfg data_if_agent_cfg;
  rand tl_agent_cfg instr_if_agent_cfg;

  `uvm_object_utils_begin(core_ibex_env_cfg)
    `uvm_field_object(data_if_agent_cfg,   UVM_DEFAULT)
    `uvm_field_object(instr_if_agent_cfg,  UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
  endfunction : new

  function void init_cfg();
    data_if_agent_cfg = tl_agent_cfg::type_id::create("data_if_agent_cfg");
    data_if_agent_cfg.is_host = 0;
    instr_if_agent_cfg = tl_agent_cfg::type_id::create("instr_if_agent_cfg");
    instr_if_agent_cfg.is_host = 0;
  endfunction

endclass
