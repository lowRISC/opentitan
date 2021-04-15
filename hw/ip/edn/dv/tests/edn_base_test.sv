// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_base_test extends cip_base_test #(
    .CFG_T(edn_env_cfg),
    .ENV_T(edn_env)
  );

  `uvm_component_utils(edn_base_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);

     configure_env();
   endfunction // build_phase

  // the base class dv_base_test creates the following instances:
  // edn_env_cfg: cfg
  // edn_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual function void configure_env();
    cfg.enable_pct = 100;
  endfunction

endclass : edn_base_test
