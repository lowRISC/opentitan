// Copyright lowRISC contributors (OpenTitan project).
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
    cfg.otp_en_cs_sw_app_read_pct        = 80;
    cfg.otp_en_cs_sw_app_read_inval_pct  = 10;
    cfg.lc_hw_debug_en_pct               = 50;
    cfg.regwen_pct                       = 100;
    cfg.enable_pct                       = 100;
    cfg.sw_app_enable_pct                = 90;
    cfg.read_int_state_pct               = 95;
    cfg.fips_force_enable_pct            = 50;
    cfg.check_int_state_pct              = 100;
    cfg.int_state_read_enable_pct        = 95;
    cfg.int_state_read_enable_regwen_pct = 50;
  endfunction

endclass : csrng_base_test
