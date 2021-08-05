// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(sram_ctrl_regs_reg_block));

  `uvm_object_utils_begin(sram_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // ext component cfgs
  rand tl_agent_cfg m_sram_cfg;
  rand push_pull_agent_cfg#(.DeviceDataWidth(KDI_DATA_SIZE)) m_kdi_cfg;

  // ext interfaces
  virtual clk_rst_if otp_clk_rst_vif;
  virtual sram_ctrl_lc_if lc_vif;
  virtual sram_ctrl_exec_if exec_vif;
  mem_bkdr_util mem_bkdr_util_h;

  // otp clk freq
  rand dv_utils_pkg::clk_freq_mhz_e otp_freq_mhz;

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = sram_ctrl_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_intg_error";
    super.initialize(csr_base_addr);

    // Build KDI cfg object and configure
    m_kdi_cfg = push_pull_agent_cfg#(.DeviceDataWidth(KDI_DATA_SIZE))::type_id::create("m_kdi_cfg");
    m_kdi_cfg.agent_type = push_pull_agent_pkg::PullAgent;
    m_kdi_cfg.if_mode = dv_utils_pkg::Device;

    // CDC synchronization between OTP and SRAM clock domains requires that the scrambling seed data
    // should be held for at least a few cycles before it can be safely latched by the SRAM domain.
    // Easy way to do this is just to force the push_pull_agent to hold the data until the next key
    // request is sent out.
    m_kdi_cfg.hold_d_data_until_next_req = 1'b1;

    // KDI interface will never need zero delay mode.
    // As per SRAM spec, KDI process will generally take around 800 CPU cyclesj
    m_kdi_cfg.zero_delays.rand_mode(0);

    // Build SRAM TL cfg object
    m_sram_cfg = tl_agent_cfg::type_id::create("m_sram_cfg");
    m_sram_cfg.if_mode = dv_utils_pkg::Host;
  endfunction

  // utility function to zero protocol delays for the TLUL agent
  // that is bound to the SRAM memory interface
  virtual function void cfg_sram_zero_delays(bit enable);
    int min = enable ? 0 : 1;
    int max = enable ? 0 : 10;

    m_sram_cfg.a_valid_delay_min = min;
    m_sram_cfg.a_valid_delay_max = max;

    m_sram_cfg.a_ready_delay_min = min;
    m_sram_cfg.a_ready_delay_max = max;

    m_sram_cfg.d_valid_delay_min = min;
    m_sram_cfg.d_valid_delay_max = max;

    m_sram_cfg.d_ready_delay_min = min;
    m_sram_cfg.d_ready_delay_max = max;
  endfunction

endclass
