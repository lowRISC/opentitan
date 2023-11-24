// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_env_cfg extends cip_base_env_cfg #(.RAL_T(alert_handler_reg_block));

  // ext component cfgs
  esc_en_vif               esc_en_vif;
  crashdump_vif            crashdump_vif;
  alert_handler_vif        alert_handler_vif;
  rand alert_esc_agent_cfg alert_host_cfg[];
  rand alert_esc_agent_cfg esc_device_cfg[];

  `uvm_object_utils_begin(alert_handler_env_cfg)
    `uvm_field_array_object(alert_host_cfg, UVM_DEFAULT)
    `uvm_field_array_object(esc_device_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    num_edn = 1;
    super.initialize(csr_base_addr);
    shadow_update_err_status_fields[ral.loc_alert_cause[LocalShadowRegUpdateErr].la] = 1;
    shadow_storage_err_status_fields[ral.loc_alert_cause[LocalShadowRegStorageErr].la] = 1;

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();

    alert_host_cfg = new[NUM_ALERTS];
    esc_device_cfg = new[NUM_ESCS];
    foreach (alert_host_cfg[i]) begin
      alert_host_cfg[i] =
          alert_esc_agent_cfg::type_id::create($sformatf("alert_host_cfg[%0d]", i));
      alert_host_cfg[i].if_mode = dv_utils_pkg::Host;
      alert_host_cfg[i].is_async = ASYNC_ON[i];
    end
    foreach (esc_device_cfg[i]) begin
      esc_device_cfg[i] =
          alert_esc_agent_cfg::type_id::create($sformatf("esc_device_cfg[%0d]", i));
      esc_device_cfg[i].if_mode  = dv_utils_pkg::Device;
      esc_device_cfg[i].is_alert = 0;
    end
    // only support 1 outstanding TL items in tlul_adapter
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  // Override shadow register naming checks. The alert handler does not expose any alert signals,
  // hence no alerts are defined in Hjson.
  virtual function void check_shadow_reg_alerts();
    // Nothing to check.
  endfunction

endclass
