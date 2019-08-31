// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_test extends dv_base_test #(
    .ENV_T(chip_env),
    .CFG_T(chip_env_cfg)
  );
  `uvm_component_utils(chip_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // chip_env_cfg: cfg
  // chip_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // knob to en/dis stubbing cpu (disabled by default)
    void'($value$plusargs("stub_cpu=%0b", cfg.stub_cpu));
  endfunction : build_phase


endclass : chip_base_test
