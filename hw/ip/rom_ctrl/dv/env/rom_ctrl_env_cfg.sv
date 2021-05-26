// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rom_ctrl_regs_reg_block));

  // ext component cfgs
  kmac_app_agent_cfg m_kmac_agent_cfg;

  // Memory backdoor util instance for ROM.
  mem_bkdr_util mem_bkdr_util_h;

  // ext interfaces
  rom_ctrl_vif rom_ctrl_vif;

  `uvm_object_utils_begin(rom_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rom_ctrl_env_pkg::LIST_OF_ALERTS;
    ral_model_names.push_back("rom_ctrl_rom_reg_block");
    super.initialize(csr_base_addr);
    num_interrupts = 0;

    m_kmac_agent_cfg = kmac_app_agent_cfg::type_id::create("m_kmac_agent_cfg");
    m_kmac_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_kmac_agent_cfg.start_default_device_seq = 1'b1;

  endfunction

endclass
