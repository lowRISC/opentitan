// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_env_cfg #(type RAL_T = dv_base_reg_block) extends dv_base_env_cfg #(RAL_T);
  // Downstream agent cfg objects.
  rand tl_agent_cfg   m_tl_agent_cfg;
  alert_esc_agent_cfg m_alert_agent_cfg[string];
  push_pull_agent_cfg#(.DeviceDataWidth(EDN_DATA_WIDTH)) m_edn_pull_agent_cfg;

  // EDN clk freq setting, if EDN is present.
  rand clk_freq_mhz_e edn_clk_freq_mhz;

  // Common interfaces - intrrupts, alerts, edn clk.
  intr_vif    intr_vif;
  devmode_vif devmode_vif;
  virtual clk_rst_if  edn_clk_rst_vif;

  // en_devmode default sets to 1 because all IPs' devmode_i is tied off internally to 1
  // TODO: enable random drive devmode once design supports
  bit  has_devmode = 1;
  bit  en_devmode = 1;
  bit  has_edn = 0;

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
    // Create downstream agent cfg objects.
    m_tl_agent_cfg = tl_agent_cfg::type_id::create("m_tl_agent_cfg");
    m_tl_agent_cfg.if_mode = dv_utils_pkg::Host;
    // TL host cannot support device same cycle response. Host may drive d_ready=0 when a_valid=1.
    m_tl_agent_cfg.host_can_stall_rsp_when_a_valid_high = $urandom_range(0, 1);

    check_shadow_reg_alerts();
    if (list_of_alerts.size() > 0) begin
      check_alert_configs();
      foreach(list_of_alerts[i]) begin
        string alert_name = list_of_alerts[i];
        // TODO: fix obj name
        m_alert_agent_cfg[alert_name] = alert_esc_agent_cfg::type_id::create("m_alert_agent_cfg");
        `DV_CHECK_RANDOMIZE_FATAL(m_alert_agent_cfg[alert_name])
        m_alert_agent_cfg[alert_name].if_mode = dv_utils_pkg::Device;
        m_alert_agent_cfg[alert_name].is_async = 1; // default async_on, can override this
        m_alert_agent_cfg[alert_name].en_ping_cov = 0;
      end
    end

    if (has_edn) begin
      m_edn_pull_agent_cfg = push_pull_agent_cfg#(.DeviceDataWidth(EDN_DATA_WIDTH))::type_id::
                             create("m_edn_pull_agent_cfg");
      `DV_CHECK_RANDOMIZE_FATAL(m_edn_pull_agent_cfg)
      m_edn_pull_agent_cfg.agent_type = PullAgent;
      m_edn_pull_agent_cfg.if_mode    = Device;
      m_edn_pull_agent_cfg.hold_d_data_until_next_req = 1;
    end
  endfunction

  virtual function void check_alert_configs();
    dv_base_reg_block sub_blks[$];
    ral.get_dv_base_reg_blocks(sub_blks);

    // For top-level, check alert_configs by each sub-block that triggers alerts.
    if (sub_blks.size() > 0) begin
      foreach(sub_blks[i]) begin
        // top-level alert name is consist of ${block_name}_${alert_name}
        // the following logic will take ${alert_name} in each block into a alerts_q and compare
        // against the block's alert_test field names
        string alerts_q[$];
        string blk_name = sub_blks[i].get_name();
        foreach (list_of_alerts[j]) begin
          string alert_name = list_of_alerts[j];
          if (alert_name.substr(0, blk_name.len() - 1) == blk_name) begin
            alerts_q.push_back(alert_name.substr(blk_name.len() + 1, list_of_alerts[j].len() - 1));
          end
        end
        if (alerts_q.size() > 0) check_alert_configs_by_block(sub_blks[i], alerts_q);
      end
    end else begin
      // For IP level testbench, directly use ral as dv_base_reg_block object.
      string alerts_q[$] = list_of_alerts;
      check_alert_configs_by_block(ral, alerts_q);
    end
  endfunction

  // Checks if the hardcoded cfg.list_of_alerts array matches the information in corresponding
  // alert_test register.
  virtual function void check_alert_configs_by_block(dv_base_reg_block blk,
                                                     const ref string  alert_names[$]);
    dv_base_reg alert_test_csr;
    alert_test_csr = blk.get_dv_base_reg_by_name("alert_test");
    `DV_CHECK_NE_FATAL(alert_test_csr, null,
                       $sformatf("cannot find alert_test csr in %0s", blk.get_name()))

    `DV_CHECK_EQ(alert_test_csr.get_n_used_bits(), alert_names.size(),
                 "alert_test field number and list_of_alerts size mismatch")

    foreach(alert_names[i]) begin
      uvm_reg_field alert_test_field = blk.get_field_by_name(alert_names[i]);
      `DV_CHECK_NE_FATAL(alert_test_field, null, $sformatf("cannot find field %s", alert_names[i]))
      `DV_CHECK_EQ(alert_test_field.get_lsb_pos(), i,
                   $sformatf("alert %0s position does not match", alert_names[i]))
    end
  endfunction

  // This function retrieves all shadowed registers in the design, then check:
  // - If the update error and storage error alerts are assigned to each shadowed register
  // - If input alert names are within the cfg.list_of_alerts
  virtual function void check_shadow_reg_alerts();
    dv_base_reg shadowed_csrs[$];
    string update_err_alert_name, storage_err_alert_name;

    ral.get_shadowed_regs(shadowed_csrs);
    foreach (shadowed_csrs[i]) begin
      update_err_alert_name = shadowed_csrs[i].get_update_err_alert_name();
      storage_err_alert_name = shadowed_csrs[i].get_storage_err_alert_name();

      if (update_err_alert_name == "" || storage_err_alert_name == "") begin
        `uvm_fatal(shadowed_csrs[i].get_full_name,
                   "please add update_err and storage_err alert names in Hjson!")
      end

      // check if alert names are valid
      if (!(update_err_alert_name inside {list_of_alerts})) begin
        `uvm_fatal(shadowed_csrs[i].get_full_name, $sformatf(
                   "update_err alert name %0s not in list_of_alerts", update_err_alert_name))
      end
      if (!(storage_err_alert_name inside {list_of_alerts})) begin
        `uvm_fatal(shadowed_csrs[i].get_full_name, $sformatf(
                   "storage_err alert name %0s not in list_of_alerts", storage_err_alert_name))
      end
    end

  endfunction

 endclass
