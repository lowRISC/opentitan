// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_env_cfg extends cip_base_env_cfg #(.RAL_T(dma_reg_block));
  // TL Port Configuration
  tl_agent_cfg          m_tl_agent_dma_host_device_cfg;
  tl_agent_cfg          m_tl_agent_dma_xbar_device_cfg;

  // Interface
  dma_vif               dma_vif;
  virtual clk_rst_if    clk_rst_vif;

  // Scoreboard
  dma_scoreboard        scoreboard_h;

  // Constraints
  //  TODO

  `uvm_object_utils_begin(dma_env_cfg)
    `uvm_field_object(m_tl_agent_dma_host_device_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_agent_dma_xbar_device_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  // Function for Initialization
  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = dma_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // TL Agent Configuration - Non RAL
    m_tl_agent_dma_host_device_cfg  =
      tl_agent_cfg::type_id::create("m_tl_agent_dma_host_device_cfg");
    m_tl_agent_dma_host_device_cfg.max_outstanding_req = dma_env_pkg::NUM_MAX_OUTSTANDING_REQS;
    m_tl_agent_dma_host_device_cfg.if_mode = dv_utils_pkg::Device;
    m_tl_agent_dma_host_device_cfg.d_valid_delay_min = 1;
    m_tl_agent_dma_host_device_cfg.d_valid_delay_max = 4; // Arbitrary

    m_tl_agent_dma_xbar_device_cfg  =
      tl_agent_cfg::type_id::create("m_tl_agent_dma_xbar_device_cfg");
    m_tl_agent_dma_xbar_device_cfg.max_outstanding_req = dma_env_pkg::NUM_MAX_OUTSTANDING_REQS;
    m_tl_agent_dma_xbar_device_cfg.if_mode = dv_utils_pkg::Device;
    m_tl_agent_dma_xbar_device_cfg.d_valid_delay_min = 1;
    m_tl_agent_dma_xbar_device_cfg.d_valid_delay_max = 4; // Arbitrary

    // TL Agent Configuration - RAL based
    m_tl_agent_cfg.max_outstanding_req = 1;

  endfunction: initialize

endclass
