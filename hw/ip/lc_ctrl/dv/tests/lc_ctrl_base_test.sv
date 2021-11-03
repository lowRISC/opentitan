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
    super.build_phase(phase);

    // Enable JTAG TAP CSR access via command line option
    void'($value$plusargs("jtag_csr=%0b", cfg.jtag_csr));

    // Report catcher
    m_report_catcher = lc_ctrl_report_catcher::type_id::create(
        {get_full_name(), ".m_report_catcher"});
    uvm_report_cb::add(null, m_report_catcher);

  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    uvm_reg r, regs[$];
    uvm_reg_block blk;
    lc_ctrl_jtag_reg_frontdoor_seq ftdr;
    super.connect_phase(phase);

    if (cfg.jtag_csr) begin
      // Set JTAG frontdoor on register model
      foreach (cfg.ral_models[i]) begin
        cfg.ral_models[i].get_registers(regs);
        while (regs.size()) begin
          r = regs.pop_front();
          ftdr = lc_ctrl_jtag_reg_frontdoor_seq::type_id::
              create($sformatf("%s.jtag_frontdoor", r.get_full_name()));
          ftdr.sequencer = env.m_jtag_riscv_agent.sequencer;
          r.set_frontdoor(.ftdr(ftdr));
          `uvm_info(`gfn,{"Set Jtag frontdoor sequence for register ",
              r.get_full_name()}, UVM_LOW)
        end
      end
      // If we are operataing with a custom frontdoor sequence demote the field access warning
      m_report_catcher.add_change_sev("RegModel",
          "\s*Individual field access not available for field.*", UVM_INFO);

      csr_utils_pkg::max_outstanding_accesses = 1;
    end

  endfunction

endclass : lc_ctrl_base_test
