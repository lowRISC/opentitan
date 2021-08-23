// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_env_cfg extends cip_base_env_cfg #(
  .RAL_T(rstmgr_reg_block)
);

  // ext component cfgs

  `uvm_object_utils_begin(rstmgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual rstmgr_if rstmgr_vif;
  virtual pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_vif;
  virtual clk_rst_if aon_clk_rst_vif;
  virtual clk_rst_if io_clk_rst_vif;
  virtual clk_rst_if io_div2_clk_rst_vif;
  virtual clk_rst_if io_div4_clk_rst_vif;
  virtual clk_rst_if main_clk_rst_vif;
  virtual clk_rst_if usb_clk_rst_vif;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rstmgr_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
  endfunction

endclass
