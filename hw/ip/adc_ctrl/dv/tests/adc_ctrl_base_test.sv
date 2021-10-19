// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_base_test extends cip_base_test #(
  .CFG_T(adc_ctrl_env_cfg),
  .ENV_T(adc_ctrl_env)
);

  // Should we print the RAL
  bit m_print_ral;


  `uvm_component_utils(adc_ctrl_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // adc_ctrl_env_cfg: cfg
  // adc_ctrl_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done
  virtual function void build_phase(uvm_phase phase);
    // Defaults - can be overridden by plusargs
    max_quit_count  = 50;
    test_timeout_ns = 600_000_000; // 600ms
    m_print_ral     = 0;

    super.build_phase(phase);
    
    // Enable RAL printout
    void'($value$plusargs("print_ral=%0b", m_print_ral));

    // Set zero delays if requested
    if(cfg.zero_delays) begin
      cfg.m_ast_adc_agent_cfg.resp_dly_min = 0;
      cfg.m_ast_adc_agent_cfg.resp_dly_max = 0;
    end

    uvm_config_db#(ast_adc_agent_cfg)::set(this, "env.m_ast_adc_agent", 
      "cfg", cfg.m_ast_adc_agent_cfg);
 
    // Print RAL if requested
    if(m_print_ral) begin
      `uvm_info(`gfn, cfg.ral.sprint(), UVM_LOW)
    end

    // Print test config
    `uvm_info(`gfn, cfg.sprint(), UVM_LOW)

  endfunction

endclass : adc_ctrl_base_test
