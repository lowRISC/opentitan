// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(otp_ctrl_reg_block));

  // ext component cfgs
  rand push_pull_agent_cfg#(SRAM_DATA_SIZE)  m_sram_pull_agent_cfg[NumSramKeyReqSlots];
  rand push_pull_agent_cfg#(OTBN_DATA_SIZE)  m_otbn_pull_agent_cfg;
  rand push_pull_agent_cfg#(FLASH_DATA_SIZE) m_flash_data_pull_agent_cfg;
  rand push_pull_agent_cfg#(FLASH_DATA_SIZE) m_flash_addr_pull_agent_cfg;

  // ext interfaces
  pwr_otp_vif         pwr_otp_vif;
  lc_provision_en_vif lc_provision_en_vif;
  lc_dft_en_vif       lc_dft_en_vif;
  mem_bkdr_vif        mem_bkdr_vif;

  `uvm_object_utils_begin(otp_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // create push_pull agent config obj
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      string cfg_name = $sformatf("sram_pull_agent_cfg[%0d]", i);
      m_sram_pull_agent_cfg[i] = push_pull_agent_cfg#(SRAM_DATA_SIZE)::type_id::create(cfg_name);
      m_sram_pull_agent_cfg[i].agent_type = PullAgent;
    end

    m_otbn_pull_agent_cfg = push_pull_agent_cfg#(OTBN_DATA_SIZE)::type_id::create
                            ("m_otbn_pull_agent_cfg");
    m_otbn_pull_agent_cfg.agent_type = PullAgent;

    m_flash_data_pull_agent_cfg = push_pull_agent_cfg#(FLASH_DATA_SIZE)::type_id::create
                                  ("m_flash_data_pull_agent_cfg");
    m_flash_data_pull_agent_cfg.agent_type = PullAgent;
    m_flash_addr_pull_agent_cfg = push_pull_agent_cfg#(FLASH_DATA_SIZE)::type_id::create
                                  ("m_flash_addr_pull_agent_cfg");
    m_flash_addr_pull_agent_cfg.agent_type = PullAgent;

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
