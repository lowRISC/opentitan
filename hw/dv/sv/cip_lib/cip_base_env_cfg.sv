// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_env_cfg #(type RAL_T = dv_base_reg_block) extends dv_base_env_cfg #(RAL_T);
  // ext component cfgs
  rand tl_agent_cfg        m_tl_agent_cfg;
  rand alert_esc_agent_cfg m_alert_agent_cfg[string];

  // common interfaces - intrrupts and alerts
  intr_vif    intr_vif;
  devmode_vif devmode_vif;

  // en_devmode default sets to 1 because all IPs' devmode_i is tied off internally to 1
  // TODO: enable random drive devmode once design supports
  bit  has_devmode = 1;
  bit  en_devmode = 1;

  uint num_interrupts;

  // if module has alerts, this list_of_alerts needs to override in cfg before super.initialize()
  // function is called
  string list_of_alerts[] = {};

  `uvm_object_param_utils_begin(cip_base_env_cfg #(RAL_T))
    `uvm_field_object          (m_tl_agent_cfg,    UVM_DEFAULT)
    `uvm_field_aa_object_string(m_alert_agent_cfg, UVM_DEFAULT)
    `uvm_field_int             (num_interrupts,    UVM_DEFAULT)
 `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [BUS_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // create tl agent config obj
    m_tl_agent_cfg = tl_agent_cfg::type_id::create("m_tl_agent_cfg");
    m_tl_agent_cfg.if_mode = dv_utils_pkg::Host;
    // host can't support device same cycle response and host may drive d_ready=0 when a_valid=1
    m_tl_agent_cfg.host_can_stall_rsp_when_a_valid_high = $urandom_range(0, 1);

    // create alert_esc_agent_cfg if the module has alerts
    foreach(list_of_alerts[i]) begin
      string alert_name = list_of_alerts[i];
      m_alert_agent_cfg[alert_name] = alert_esc_agent_cfg::type_id::create("m_alert_agent_cfg");
      m_alert_agent_cfg[alert_name].if_mode = dv_utils_pkg::Device;
      m_alert_agent_cfg[alert_name].en_ping_cov = 0;
      if (zero_delays) begin
        m_alert_agent_cfg[alert_name].alert_delay_min = 0;
        m_alert_agent_cfg[alert_name].alert_delay_max = 0;
      end
    end
  endfunction

endclass
