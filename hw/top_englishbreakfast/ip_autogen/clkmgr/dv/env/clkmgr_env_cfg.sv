// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_env_cfg extends cip_base_env_cfg #(
  .RAL_T(clkmgr_reg_block)
);

  // This scoreboard handle is used to flag expected errors.
  clkmgr_scoreboard  scoreboard;

  // ext component cfgs

  // ext interfaces
  virtual clkmgr_if      clkmgr_vif;
  virtual clkmgr_csrs_if clkmgr_csrs_vif;
  virtual clk_rst_if     main_clk_rst_vif;
  virtual clk_rst_if     io_clk_rst_vif;
  virtual clk_rst_if     usb_clk_rst_vif;
  virtual clk_rst_if     aon_clk_rst_vif;

  virtual clk_rst_if root_io_clk_rst_vif;
  virtual clk_rst_if root_main_clk_rst_vif;
  virtual clk_rst_if root_usb_clk_rst_vif;

  `uvm_object_utils_begin(clkmgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = clkmgr_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // This is for the integrity error test.
    tl_intg_alert_name = "fatal_fault";
    tl_intg_alert_fields[ral.fatal_err_code.reg_intg] = 1;
    m_tl_agent_cfg.max_outstanding_req = 1;

    // shadow registers
    shadow_update_err_status_fields[ral.recov_err_code.shadow_update_err] = 1;
    shadow_storage_err_status_fields[ral.fatal_err_code.shadow_storage_err] = 1;
  endfunction

endclass
