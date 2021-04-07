// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_base_test extends cip_base_test #(
  .CFG_T(pwm_env_cfg),
  .ENV_T(pwm_env)
);

  `uvm_component_utils(pwm_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // pwm_env_cfg: cfg
  // pwm_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done
  virtual function void build_phase(uvm_phase phase);
    max_quit_count  = 50;
    test_timeout_ns = 600_000_000;  // 600ms
    super.build_phase(phase);
  endfunction : build_phase

endclass : pwm_base_test
