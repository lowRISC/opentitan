// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_base_test extends cip_base_test #(
    .CFG_T(lc_ctrl_env_cfg),
    .ENV_T(lc_ctrl_env)
  );

  lc_ctrl_report_catcher m_report_catcher;

  `uvm_component_utils(lc_ctrl_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);

    // Need to demote warnings before calling super.build()
    // Report catcher
    m_report_catcher = lc_ctrl_report_catcher::type_id::create(
        {get_full_name(), ".m_report_catcher"});
    uvm_report_cb::add(null, m_report_catcher);

    // Add demoted messages
    add_demotes();

    super.build_phase(phase);

    // Enable JTAG TAP CSR access via command line option
    void'($value$plusargs("jtag_csr=%0b", cfg.jtag_csr));

  endfunction : build_phase

  virtual function void add_demotes();
    // Demote field access warnings to infos
    m_report_catcher.add_change_sev("RegModel",
        "\s*Individual field access not available for field.*", UVM_INFO);

    // Demote field access warnings to infos
    m_report_catcher.add_change_sev("RegModel",
        "\s*Target bus does not support byte enabling.*", UVM_INFO);

    // Demote address maps warnings
    m_report_catcher.add_change_sev("RegModel",
      "\s*map .* does not seem to be initialized correctly.*", UVM_INFO);

  endfunction

endclass : lc_ctrl_base_test
