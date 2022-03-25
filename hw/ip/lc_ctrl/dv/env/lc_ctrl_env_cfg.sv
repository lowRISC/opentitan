// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_env_cfg extends cip_base_env_cfg #(
  .RAL_T(lc_ctrl_reg_block)
);
  // DUT parameters
  lc_ctrl_parameters_cfg parameters_cfg;

  // ext component cfgs
  push_pull_agent_cfg #(
    .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
    .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
  ) m_otp_prog_pull_agent_cfg;
  alert_esc_agent_cfg m_esc_scrap_state1_agent_cfg;
  alert_esc_agent_cfg m_esc_scrap_state0_agent_cfg;
  jtag_riscv_agent_cfg m_jtag_riscv_agent_cfg;
  kmac_app_agent_cfg m_kmac_app_agent_cfg;

  // ext interfaces
  pwr_lc_vif pwr_lc_vif;
  lc_ctrl_vif lc_ctrl_vif;

  // Use JTAG for register accesses
  // TODO: use multiple address maps
  bit jtag_csr;
  // Error injection configuration
  lc_ctrl_err_inj_t err_inj;

  // Alert events - these are triggered in the scoreboard
  event fatal_prog_error_ev;
  event fatal_state_error_ev;
  event fatal_bus_integ_error_ev;
  // Test phase - used to synchronise scoreboard
  lc_ctrl_test_phase_e test_phase;
  // Test phase has been set event
  event set_test_phase_ev;
  // Max delay for alerts in clocks
  uint alert_max_delay;
  // Enable scoreboard ral update on write
  bit en_scb_ral_update_write = 1;

  // OTP
  rand otp_device_id_t otp_device_id;
  rand otp_device_id_t otp_manuf_state;
  rand logic [OtpTestCtrlWidth-1:0] otp_vendor_test_ctrl;
  rand logic [OtpTestStatusWidth-1:0] otp_vendor_test_status;



  `uvm_object_utils_begin(lc_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = lc_ctrl_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_bus_integ_error";
    sec_cm_alert_name = "fatal_state_error";
    super.initialize(csr_base_addr);

    // Find parameters on config db
    if (!uvm_config_db#(lc_ctrl_parameters_cfg)::get(
            null, "", "parameters_cfg", parameters_cfg
        ) || parameters_cfg == null) begin
      `uvm_fatal(get_full_name(), "failed to get parameters_cfg from uvm_config_db")
    end

    m_otp_prog_pull_agent_cfg = push_pull_agent_cfg#(
      .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
      .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
    )::type_id::create(
        "m_otp_prog_pull_agent_cfg"
    );
    `DV_CHECK_RANDOMIZE_FATAL(m_otp_prog_pull_agent_cfg)
    m_otp_prog_pull_agent_cfg.agent_type = PullAgent;
    m_otp_prog_pull_agent_cfg.if_mode = Device;
    m_otp_prog_pull_agent_cfg.in_bidirectional_mode = 1;


    m_esc_scrap_state1_agent_cfg =
        alert_esc_agent_cfg::type_id::create("m_esc_scrap_state1_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_scrap_state1_agent_cfg)
    m_esc_scrap_state1_agent_cfg.is_alert = 0;

    m_esc_scrap_state0_agent_cfg =
        alert_esc_agent_cfg::type_id::create("m_esc_scrap_state0_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_scrap_state0_agent_cfg)
    m_esc_scrap_state0_agent_cfg.is_alert = 0;

    m_jtag_riscv_agent_cfg = jtag_riscv_agent_cfg::type_id::create("m_jtag_riscv_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_jtag_riscv_agent_cfg)

    m_kmac_app_agent_cfg = kmac_app_agent_cfg::type_id::create("m_kmac_app_agent_cfg");
    m_kmac_app_agent_cfg.if_mode = Device;
    m_kmac_app_agent_cfg.req_delay_max = 20;
    m_kmac_app_agent_cfg.rsp_delay_max = 20;
    `DV_CHECK_RANDOMIZE_FATAL(m_kmac_app_agent_cfg)

    jtag_csr = 0;

    alert_max_delay = 2000;
  endfunction

  virtual function void set_test_phase(lc_ctrl_test_phase_e test_phase);
    // Set in config object
    this.test_phase = test_phase;
    // And interface
    lc_ctrl_vif.test_phase <= test_phase;
    ->set_test_phase_ev;
  endfunction

  virtual function lc_ctrl_test_phase_e get_test_phase();
    return (this.test_phase);
  endfunction

  // Use these functions to propagate in_reset to JTAG RISCV agents
  virtual function void reset_asserted();
    super.reset_asserted();
    m_jtag_riscv_agent_cfg.in_reset = 1;
  endfunction

  virtual function void reset_deasserted();
    super.reset_deasserted();
    m_jtag_riscv_agent_cfg.in_reset = 0;
  endfunction

endclass
