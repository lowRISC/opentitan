// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(sram_ctrl_reg_block));

  `uvm_object_utils_begin(sram_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // ext component cfgs
  rand tl_agent_cfg m_sram_cfg;
  rand push_pull_agent_cfg#(.DeviceDataWidth(KDI_DATA_SIZE)) m_kdi_cfg;

  // ext interfaces
  virtual clk_rst_if otp_clk_rst_vif;
  lc_vif lc_vif;
  mem_bkdr_vif mem_bkdr_vif;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = sram_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // Build KDI cfg object
    m_kdi_cfg = push_pull_agent_cfg#(.DeviceDataWidth(KDI_DATA_SIZE))::type_id::create("m_kdi_cfg");

    // Build SRAM TL cfg object
    m_sram_cfg = tl_agent_cfg::type_id::create("m_sram_cfg");
  endfunction

endclass
