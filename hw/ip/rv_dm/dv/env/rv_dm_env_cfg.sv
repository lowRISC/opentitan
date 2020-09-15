// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env_cfg extends dv_base_env_cfg #(.RAL_T(rv_dm_reg_block));

  // ext component cfgs
  rand jtag_agent_cfg     m_jtag_agent_cfg;
  rand tl_agent_cfg       m_tl_host_agent_cfg;
  rand tl_agent_cfg       m_tl_device_agent_cfg;

  virtual rv_dm_if        rv_dm_vif;

  `uvm_object_utils_begin(rv_dm_env_cfg)
    `uvm_field_object(m_jtag_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_host_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_device_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // create jtag agent config obj
    m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
    // create tl_host agent config obj
    m_tl_host_agent_cfg = tl_agent_cfg::type_id::create("m_tl_host_agent_cfg");
    m_tl_host_agent_cfg.if_mode = dv_utils_pkg::Host;
    m_tl_host_agent_cfg.is_active = 1'b1;
    // create tl_device agent config obj
    m_tl_device_agent_cfg = tl_agent_cfg::type_id::create("m_tl_device_agent_cfg");
    m_tl_device_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_tl_device_agent_cfg.is_active = 1'b1;
  endfunction

endclass
