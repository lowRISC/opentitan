// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_env_cfg extends cip_base_env_cfg #(.RAL_T(keymgr_reg_block));

  rand kmac_app_agent_cfg m_keymgr_kmac_agent_cfg;

  keymgr_scoreboard scb;
  // interface for input data from LC, OTP and flash
  keymgr_vif keymgr_vif;

  `uvm_object_utils_begin(keymgr_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = keymgr_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_fault_err";
    sec_cm_alert_name  = tl_intg_alert_name;
    num_edn = 1;
    super.initialize(csr_base_addr);
    tl_intg_alert_fields[ral.fault_status.regfile_intg] = 1;
    shadow_update_err_status_fields[ral.err_code.invalid_shadow_update] = 1;
    shadow_storage_err_status_fields[ral.fault_status.shadow] = 1;

    m_keymgr_kmac_agent_cfg = kmac_app_agent_cfg::type_id::create("m_keymgr_kmac_agent_cfg");
    m_keymgr_kmac_agent_cfg.if_mode = dv_utils_pkg::Device;

    // keymgr requests entropy periodically, if seq is done, don't need to add any delay due to
    // activity from EDN interface
    m_edn_pull_agent_cfgs[0].ok_to_end_delay_ns = 0;

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

endclass
