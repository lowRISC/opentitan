// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_base_test extends cip_base_test #(
  .CFG_T(lc_ctrl_env_cfg),
  .ENV_T(lc_ctrl_env)
);

  `uvm_component_utils(lc_ctrl_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Enable JTAG TAP CSR access via command line option
    void'($value$plusargs("jtag_csr=%0b", cfg.jtag_csr));

    // Increase alert wait time if using JTAG
    if (cfg.jtag_csr) cfg.alert_max_delay = 15000;

  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // Run a sequence in m_kmac_app_agent that will respond with to requests with digests
    //
    // This gets run in the background: it will run forever and we want to be able to finish the
    // test when the rest of run_phase completes.
    fork
      env.m_kmac_app_agent.run_device_seq();
    join_none

    super.run_phase(phase);
  endtask

  // Add message demotes here
  virtual function void add_message_demotes(dv_report_catcher catcher);
    string msg;

    super.add_message_demotes(catcher);

    // Demote field access warnings to infos
    msg = "\s*Individual field access not available for field.*";
    catcher.add_change_sev("RegModel", msg, UVM_INFO);

    // Demote field access warnings to infos
    msg = "\s*Target bus does not support byte enabling.*";
    catcher.add_change_sev("RegModel", msg, UVM_INFO);

    // Demote field busy warning
    msg = {
      "\s*Setting the value of field \".*\" while containing",
      "\s+register \"lc_ctrl_regs_reg_block.alert_test\" is being accessed"
    };
    catcher.add_change_sev("UVM/FLD/SET/BSY", msg, UVM_INFO);

  endfunction

endclass : lc_ctrl_base_test
