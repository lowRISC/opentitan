// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_env_cfg extends cip_base_env_cfg #(
  .RAL_T(pwrmgr_reg_block)
);

  // ext component cfgs
  alert_esc_agent_cfg m_esc_agent_cfg;

  `uvm_object_utils_begin(pwrmgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // ext interfaces
  virtual clk_rst_if slow_clk_rst_vif;
  virtual pwrmgr_if pwrmgr_vif;
  virtual pwrmgr_ast_sva_if pwrmgr_ast_sva_vif;
  virtual pwrmgr_clock_enables_sva_if pwrmgr_clock_enables_sva_vif;
  virtual pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_vif;

  // The run_phase object, to deal with objections.
  uvm_phase run_phase;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = pwrmgr_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    num_interrupts = ral.intr_state.get_n_used_bits();
    `ASSERT_I(NumInstrMatch_A, num_interrupts == NUM_INTERRUPTS)
    `uvm_info(`gfn, $sformatf("num_interrupts = %0d", num_interrupts), UVM_MEDIUM)
    tl_intg_alert_fields[ral.fault_status.reg_intg_err] = 1;
    m_tl_agent_cfg.max_outstanding_req = 1;
    m_esc_agent_cfg = alert_esc_agent_cfg::type_id::create("m_esc_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_agent_cfg)
    m_esc_agent_cfg.is_alert = 0;
    // Disable escalation ping coverage.
    m_esc_agent_cfg.en_ping_cov = 0;
  endfunction

endclass
