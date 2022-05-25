// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_env_cfg extends dv_base_env_cfg;

  // If set, the scoreboard won't check caching ratios
  bit disable_caching_ratio_test = 0;

  // ext component cfgs
  rand ibex_icache_core_agent_cfg   core_agent_cfg;
  rand ibex_icache_mem_agent_cfg    mem_agent_cfg;

  rand scrambling_key_agent_cfg     scrambling_key_cfg;
  ibex_icache_ram_vif ram_if;

  // Force the clock frequency to 50MHz. The clock frequency doesn't really matter for ICache
  // testing and 50MHz dumped waves are nice to read because clock edges are multiples of 10ns.
  constraint clk_freq_50_c {
    clk_freq_mhz == 50;
  }

  `uvm_object_utils_begin(ibex_icache_env_cfg)
    `uvm_field_object      (core_agent_cfg,      UVM_DEFAULT)
    `uvm_field_object      (mem_agent_cfg,       UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name="");
    super.new(name);
  endfunction

  virtual function void initialize(bit [BUS_AW-1:0] csr_base_addr = '1);
    ral_model_names = {}; // The ICache has no RAL model
    super.initialize(csr_base_addr);

    core_agent_cfg     = ibex_icache_core_agent_cfg::type_id::create("core_agent_cfg");
    mem_agent_cfg      = ibex_icache_mem_agent_cfg::type_id::create ("mem_agent_cfg");
    scrambling_key_cfg = scrambling_key_agent_cfg::type_id::create("scrambling_key_cfg");

  endfunction

endclass
