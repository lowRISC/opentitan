// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_env_cfg extends dv_base_env_cfg;

  // If set, the scoreboard won't check caching ratios
  bit disable_caching_ratio_test = 0;

  // ext component cfgs
  rand ibex_icache_core_agent_cfg   core_agent_cfg;
  rand ibex_icache_mem_agent_cfg    mem_agent_cfg;

  // Force the clock frequency to 50MHz. The clock frequency doesn't really matter for ICache
  // testing and 50MHz dumped waves are nice to read because clock edges are multiples of 10ns.
  constraint clk_freq_50_c {
    clk_freq_mhz == ClkFreq50Mhz;
  }

  // Config objects for ECC components (see create_ecc_agent_cfgs). Since these are created after
  // initialization, they won't get randomized automatically, so we do that manually at the bottom
  // of create_ecc_agent_cfgs.
  ibex_icache_ecc_agent_cfg         ecc_tag_agent_cfgs[];
  ibex_icache_ecc_agent_cfg         ecc_data_agent_cfgs[];

  `uvm_object_utils_begin(ibex_icache_env_cfg)
    `uvm_field_object      (core_agent_cfg,      UVM_DEFAULT)
    `uvm_field_object      (mem_agent_cfg,       UVM_DEFAULT)
    `uvm_field_array_object(ecc_tag_agent_cfgs,  UVM_DEFAULT)
    `uvm_field_array_object(ecc_data_agent_cfgs, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    core_agent_cfg = ibex_icache_core_agent_cfg::type_id::create("core_agent_cfg");
    mem_agent_cfg  = ibex_icache_mem_agent_cfg::type_id::create ("mem_agent_cfg");
  endfunction

  // Create tag and data ECC agents for each way. If ECC is disabled, this should still be called,
  // but with num_ecc_ways = 0.
  function automatic void create_ecc_agent_cfgs(int unsigned num_ecc_ways);
    ecc_tag_agent_cfgs = new[num_ecc_ways];
    ecc_data_agent_cfgs = new[num_ecc_ways];
    for (int unsigned i = 0; i < num_ecc_ways; i++) begin
      string tname = $sformatf("ecc_tag_agent_cfgs[%0d]", i);
      string dname = $sformatf("ecc_data_agent_cfgs[%0d]", i);
      ecc_tag_agent_cfgs[i] = ibex_icache_ecc_agent_cfg::type_id::create(tname);
      ecc_data_agent_cfgs[i] = ibex_icache_ecc_agent_cfg::type_id::create(dname);

      `DV_CHECK_RANDOMIZE_FATAL(ecc_tag_agent_cfgs[i])
      `DV_CHECK_RANDOMIZE_FATAL(ecc_data_agent_cfgs[i])
    end
  endfunction

endclass
