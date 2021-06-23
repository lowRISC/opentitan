// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_env_cfg extends cip_base_env_cfg #(.RAL_T(clkmgr_reg_block));

  // ext component cfgs

  // ext interfaces
  clkmgr_vif clkmgr_vif;
  virtual clk_rst_if main_clk_rst_vif;
  virtual clk_rst_if io_clk_rst_vif;
  virtual clk_rst_if usb_clk_rst_vif;
  virtual clk_rst_if aon_clk_rst_vif;

  `uvm_object_utils_begin(clkmgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = clkmgr_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // clkmgr has no interrupts, alerts, or devmode yet.
  endfunction

endclass
