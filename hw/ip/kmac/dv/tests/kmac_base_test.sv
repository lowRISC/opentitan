// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_base_test extends cip_base_test #(
    .CFG_T(kmac_env_cfg),
    .ENV_T(kmac_env)
  );

  `uvm_component_utils(kmac_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // kmac_env_cfg: cfg
  // kmac_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    void'($value$plusargs("enable_masking=%0b", cfg.enable_masking));
  endfunction

endclass : kmac_base_test
