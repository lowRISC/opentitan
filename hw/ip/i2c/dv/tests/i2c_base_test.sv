// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_base_test extends cip_base_test #(.ENV_T(i2c_env),
                                            .CFG_T(i2c_env_cfg));
  `uvm_component_utils(i2c_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // i2c_env_cfg: cfg
  // i2c_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and
  // run that seq in the run_phase; as such, nothing more needs to be done

  virtual function void build_phase(uvm_phase phase);
    if_mode_e mode = Device;
    test_timeout_ns = 600_000_000; // 600ms
    super.build_phase(phase);
    `DV_GET_ENUM_PLUSARG(if_mode_e, mode, i2c_agent_mode)
    `uvm_info(`gfn, $sformatf("set i2c agent mode to %s", mode.name), UVM_MEDIUM)
    cfg.m_i2c_agent_cfg.if_mode = mode;
    void'($value$plusargs("use_intr_handler=%0b", cfg.use_intr_handler));
    void'($value$plusargs("slow_acq=%0b", cfg.slow_acq));
    void'($value$plusargs("i2c_wr_pct=%0d", cfg.wr_pct));
    void'($value$plusargs("i2c_rd_pct=%0d", cfg.rd_pct));
    void'($value$plusargs("i2c_bad_addr_pct=%0d", cfg.bad_addr_pct));
  endfunction : build_phase

endclass : i2c_base_test
