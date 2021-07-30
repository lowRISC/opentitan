// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_base_test extends cip_base_test #(
    .CFG_T(csrng_env_cfg),
    .ENV_T(csrng_env)
  );

  `uvm_component_utils(csrng_base_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);

     configure_env();
   endfunction

  // the base class dv_base_test creates the following instances:
  // csrng_env_cfg: cfg
  // csrng_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual function void configure_env();
    cfg.enable_pct        = 100;
    cfg.chk_int_state_pct = 100;
    cfg.cmd_length_0_pct  = 0;
    cfg.cmd_flags_0_pct   = 0;
  endfunction

endclass : csrng_base_test
