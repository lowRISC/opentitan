// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_env_cfg extends cip_base_env_cfg #(
  .RAL_T(rstmgr_reg_block)
);

  // This scoreboard handle is used to flag expected errors.
  rstmgr_scoreboard  scoreboard;

  // ext component cfgs

  `uvm_object_utils_begin(rstmgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

% for clk in sorted(list(clk_freqs.keys())):
  virtual clk_rst_if ${clk}_clk_rst_vif;
% endfor
  virtual pwrmgr_rstmgr_sva_if #(.PowerDomains(rstmgr_pkg::PowerDomains)) pwrmgr_rstmgr_sva_vif;
  virtual rstmgr_cascading_sva_if rstmgr_cascading_sva_vif;
  virtual rstmgr_if rstmgr_vif;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rstmgr_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    tl_intg_alert_fields[ral.err_code.reg_intg_err] = 1;
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

endclass
