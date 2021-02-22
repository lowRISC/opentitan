// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(otp_ctrl_reg_block));

  // ext component cfgs
  rand push_pull_agent_cfg#(.DeviceDataWidth(SRAM_DATA_SIZE))
      m_sram_pull_agent_cfg[NumSramKeyReqSlots];
  rand push_pull_agent_cfg#(.DeviceDataWidth(OTBN_DATA_SIZE))  m_otbn_pull_agent_cfg;
  rand push_pull_agent_cfg#(.DeviceDataWidth(FLASH_DATA_SIZE)) m_flash_data_pull_agent_cfg;
  rand push_pull_agent_cfg#(.DeviceDataWidth(FLASH_DATA_SIZE)) m_flash_addr_pull_agent_cfg;
  rand push_pull_agent_cfg#(.DeviceDataWidth(1), .HostDataWidth(LC_PROG_DATA_SIZE))
      m_lc_prog_pull_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth))
      m_lc_token_pull_agent_cfg;

  // ext interfaces
  mem_bkdr_vif mem_bkdr_vif;
  otp_ctrl_vif otp_ctrl_vif;

  bit backdoor_clear_mem;

  // This value is updated in sequence when backdoor inject ECC error
  otp_ecc_err_e ecc_err = OtpNoEccErr;

  `uvm_object_utils_begin(otp_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = otp_ctrl_env_pkg::LIST_OF_ALERTS;
    has_edn = 1;
    super.initialize(csr_base_addr);

    // create push_pull agent config obj
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      string cfg_name = $sformatf("sram_pull_agent_cfg[%0d]", i);
      m_sram_pull_agent_cfg[i] = push_pull_agent_cfg#(.DeviceDataWidth(SRAM_DATA_SIZE))::type_id
                                 ::create(cfg_name);
      m_sram_pull_agent_cfg[i].agent_type = PullAgent;
    end

    m_otbn_pull_agent_cfg = push_pull_agent_cfg#(.DeviceDataWidth(OTBN_DATA_SIZE))::type_id
                            ::create("m_otbn_pull_agent_cfg");
    m_otbn_pull_agent_cfg.agent_type = PullAgent;

    m_flash_data_pull_agent_cfg = push_pull_agent_cfg#(.DeviceDataWidth(FLASH_DATA_SIZE))::type_id
                                  ::create("m_flash_data_pull_agent_cfg");
    m_flash_data_pull_agent_cfg.agent_type = PullAgent;
    m_flash_addr_pull_agent_cfg = push_pull_agent_cfg#(.DeviceDataWidth(FLASH_DATA_SIZE))::type_id
                                  ::create("m_flash_addr_pull_agent_cfg");
    m_flash_addr_pull_agent_cfg.agent_type = PullAgent;

    m_lc_prog_pull_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(LC_PROG_DATA_SIZE),
                               .DeviceDataWidth(1))::type_id::create("m_lc_prog_pull_agent_cfg");
    m_lc_prog_pull_agent_cfg.agent_type = PullAgent;

    m_lc_token_pull_agent_cfg = push_pull_agent_cfg#(
                                .HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth))::type_id
                                ::create("m_lc_token_pull_agent_cfg");
    m_lc_token_pull_agent_cfg.agent_type = PullAgent;
    m_lc_token_pull_agent_cfg.in_bidirectional_mode = 1;

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
