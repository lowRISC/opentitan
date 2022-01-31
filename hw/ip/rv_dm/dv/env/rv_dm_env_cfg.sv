// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env_cfg extends cip_base_env_cfg #(.RAL_T(rv_dm_regs_reg_block));

  // ext component cfgs
  virtual rv_dm_if    rv_dm_vif;
  rand jtag_agent_cfg m_jtag_agent_cfg;
  rand tl_agent_cfg   m_tl_sba_agent_cfg;

  // A constant that can be referenced from anywhere.
  string rom_ral_name = "rv_dm_rom_reg_block";

  `uvm_object_utils_begin(rv_dm_env_cfg)
    `uvm_field_object(m_jtag_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_sba_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rv_dm_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_fault";

    // Set up second RAL model for ROM memory and associated collateral
    ral_model_names.push_back(rom_ral_name);

    // both RAL models use same clock frequency
    clk_freqs_mhz["rv_dm_rom_reg_block"] = clk_freq_mhz;

    super.initialize(csr_base_addr);
    `uvm_info(`gfn, $sformatf("ral_model_names: %0p", ral_model_names), UVM_LOW)

    // default TLUL supports 1 outstanding item, the sram TLUL supports 2 outstanding items.
    m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 1;
    m_tl_agent_cfgs[rom_ral_name].max_outstanding_req = 2;

    // Create jtag agent config obj
    m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
    m_jtag_agent_cfg.if_mode = dv_utils_pkg::Host;
    m_jtag_agent_cfg.is_active = 1'b1;

    // Create TL agent config obj for the SBA port.
    m_tl_sba_agent_cfg =  tl_agent_cfg::type_id::create("m_tl_sba_agent_cfg");
    m_tl_sba_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_tl_sba_agent_cfg.is_active = 1'b1;
  endfunction

endclass
