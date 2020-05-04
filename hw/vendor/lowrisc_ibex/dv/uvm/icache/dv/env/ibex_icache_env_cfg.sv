// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_env_cfg extends dv_base_env_cfg;

  // ext component cfgs
  rand ibex_icache_core_agent_cfg   core_agent_cfg;
  rand ibex_icache_mem_agent_cfg    mem_agent_cfg;

  `uvm_object_utils_begin(ibex_icache_env_cfg)
    `uvm_field_object(core_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(mem_agent_cfg,  UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    core_agent_cfg = ibex_icache_core_agent_cfg::type_id::create("core_agent_cfg");
    mem_agent_cfg  = ibex_icache_mem_agent_cfg::type_id::create ("mem_agent_cfg");
  endfunction

endclass
