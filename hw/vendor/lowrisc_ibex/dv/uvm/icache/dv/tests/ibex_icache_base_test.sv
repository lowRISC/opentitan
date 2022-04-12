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
    super.build_phase(phase);
  endfunction

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

endclass : ibex_icache_base_test
