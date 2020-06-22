// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_base_test extends dv_base_test #(
    .CFG_T(ibex_icache_env_cfg),
    .ENV_T(ibex_icache_env)
  );

  `uvm_component_utils(ibex_icache_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // ibex_icache_env_cfg: cfg
  // ibex_icache_env:     env

  virtual function void build_phase(uvm_phase phase);
    int unsigned num_ecc_ways;
    if (!uvm_config_db#(int unsigned)::get(this, "", "num_ecc_ways", num_ecc_ways)) begin
      `uvm_fatal(`gfn, "failed to get num_ecc_ways from uvm_config_db")
    end

    super.build_phase(phase);

    cfg.has_ral = 1'b0;

    // Create config objects for each of the ECC agents. We can't do that in the config object
    // itself (because that's not a component, so doesn't have access to the uvm_config_db).
    cfg.create_ecc_agent_cfgs(num_ecc_ways);

  endfunction

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

endclass : ibex_icache_base_test

