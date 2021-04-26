// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(lc_ctrl_reg_block));

  // ext component cfgs
  push_pull_agent_cfg#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                       .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)) m_otp_prog_pull_agent_cfg;
  push_pull_agent_cfg#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)) m_otp_token_pull_agent_cfg;
  alert_esc_agent_cfg  m_esc_wipe_secrets_agent_cfg;
  alert_esc_agent_cfg  m_esc_scrap_state_agent_cfg;
  jtag_riscv_agent_cfg m_jtag_riscv_agent_cfg;

  // ext interfaces
  pwr_lc_vif  pwr_lc_vif;
  lc_ctrl_vif lc_ctrl_vif;

  `uvm_object_utils_begin(lc_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = lc_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    m_otp_prog_pull_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
        .DeviceDataWidth(OTP_PROG_DDATA_WIDTH))::type_id::create("m_otp_prog_pull_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_otp_prog_pull_agent_cfg)
    m_otp_prog_pull_agent_cfg.agent_type            = PullAgent;
    m_otp_prog_pull_agent_cfg.if_mode               = Device;
    m_otp_prog_pull_agent_cfg.in_bidirectional_mode = 1;

    m_otp_token_pull_agent_cfg = push_pull_agent_cfg#(
                                 .HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth))
        ::type_id::create("m_otp_token_pull_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_otp_token_pull_agent_cfg)
    m_otp_token_pull_agent_cfg.agent_type                 = PullAgent;
    m_otp_token_pull_agent_cfg.if_mode                    = Device;
    m_otp_token_pull_agent_cfg.in_bidirectional_mode      = 1;
    m_otp_token_pull_agent_cfg.hold_d_data_until_next_req = 1;

    m_esc_wipe_secrets_agent_cfg = alert_esc_agent_cfg::type_id::create(
        "m_esc_wipe_secrets_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_wipe_secrets_agent_cfg)
    m_esc_wipe_secrets_agent_cfg.is_alert = 0;

    m_esc_scrap_state_agent_cfg = alert_esc_agent_cfg::type_id::create(
        "m_esc_scrap_state_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_scrap_state_agent_cfg)
    m_esc_scrap_state_agent_cfg.is_alert = 0;

    m_jtag_riscv_agent_cfg = jtag_riscv_agent_cfg::type_id::create("m_jtag_riscv_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_jtag_riscv_agent_cfg)
  endfunction

endclass
