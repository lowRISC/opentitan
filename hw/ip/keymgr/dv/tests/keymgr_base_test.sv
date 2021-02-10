// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_base_test extends cip_base_test #(
    .CFG_T(keymgr_env_cfg),
    .ENV_T(keymgr_env)
  );

  `uvm_component_utils(keymgr_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // keymgr_env_cfg: cfg
  // keymgr_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual task run_phase(uvm_phase phase);
    // keymgr requests entropy periodically, if seq is done, don't need to add any delay due to
    // activity from EDN interface which may prevent sim from finishing
    drain_time_ns = 0;
    super.run_phase(phase);
  endtask
endclass : keymgr_base_test
