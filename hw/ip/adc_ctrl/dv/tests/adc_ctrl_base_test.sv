// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_base_test extends cip_base_test #(
  .CFG_T(adc_ctrl_env_cfg),
  .ENV_T(adc_ctrl_env)
);

  `uvm_component_utils(adc_ctrl_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // adc_ctrl_env_cfg: cfg
  // adc_ctrl_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done
  virtual function void build_phase(uvm_phase phase);
    bit print_ral = 0;
    bit filters_fixed = 0;

    // Defaults - can be overridden by plusargs
    test_timeout_ns = 600_000_000;  // 600ms

    // Enable fixed filters
    void'($value$plusargs("filters_fixed=%0b", filters_fixed));

    if (!filters_fixed) begin
      // Use extended config object with variable filters
      set_type_override_by_type(adc_ctrl_env_cfg::get_type, adc_ctrl_env_var_filters_cfg::get_type);
    end

    super.build_phase(phase);

    // Enable RAL printout
    void'($value$plusargs("print_ral=%0b", print_ral));

    cfg.filters_fixed = filters_fixed;

    // Print RAL if requested
    if (print_ral) begin
      `uvm_info(`gfn, cfg.ral.sprint(), UVM_LOW)
    end

    // Disable wake up assertion - is periodically enabled by the test sequence
    `DV_ASSERT_CTRL_REQ("WakeupTime_A_CTRL", 0)

    // Print test config
    `uvm_info(`gfn, cfg.sprint(), UVM_LOW)

  endfunction

endclass : adc_ctrl_base_test
