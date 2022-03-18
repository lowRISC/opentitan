// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_base_test extends cip_base_test #(
    .CFG_T(rv_dm_env_cfg),
    .ENV_T(rv_dm_env)
  );

  `uvm_component_utils(rv_dm_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // rv_dm_env_cfg: cfg
  // rv_dm_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    test_timeout_ns = 20_000_000;  // 20ms.
  endfunction : build_phase

endclass : rv_dm_base_test
