// Copyright lowRISC contributors (OpenTitan project).
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
    cfg.disable_regwen_pct = 5;

    cfg.m_csrng_agent_cfg.cmd_zero_delays = 0; // For cmd_ack and cmd_ready
    cfg.m_csrng_agent_cfg.cmd_force_ack   = 0;
    cfg.m_csrng_agent_cfg.min_cmd_ack_dly = 4;
    cfg.m_csrng_agent_cfg.max_cmd_ack_dly = 32;
    cfg.m_csrng_agent_cfg.min_genbits_dly = 0;
    cfg.m_csrng_agent_cfg.max_genbits_dly = 32;
    cfg.m_csrng_agent_cfg.min_cmd_rdy_dly = 0;
    cfg.m_csrng_agent_cfg.max_cmd_rdy_dly = 1;
    // CSRNG should not return errors
    cfg.m_csrng_agent_cfg.rsp_sts_err     = csrng_pkg::CMD_STS_SUCCESS;
  endfunction

endclass : edn_base_test
