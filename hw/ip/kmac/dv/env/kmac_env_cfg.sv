// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_env_cfg extends cip_base_env_cfg #(.RAL_T(kmac_reg_block));

  // ext interfaces
  kmac_vif kmac_vif;

  rand kmac_app_agent_cfg m_kmac_app_agent_cfg[kmac_pkg::NumAppIntf];
  rand key_sideload_agent_cfg keymgr_sideload_agent_cfg;

  // Masked KMAC is the default configuration
  bit enable_masking = 1;

  // For the unmasked KMAC, the software key is not masked by default.
  bit sw_key_masked = 0;

  // Disable scb cycle accurate check ("status" and "intr_state" registers).
  bit do_cycle_accurate_check = 1;

  // Skip read check for some error test case
  bit skip_read_check = 0;
  // These values are used by the test vector tests to select the correct vector text files.
  // These are unused by all other tests.
  int sha3_variant;
  int shake_variant;

  `uvm_object_utils_begin(kmac_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    num_edn = 1;
    list_of_alerts = kmac_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_fault_err";
    sec_cm_alert_name  = "fatal_fault_err";
    super.initialize(csr_base_addr);

    tl_intg_alert_fields[ral.status.alert_fatal_fault] = 1;
    tl_intg_alert_fields[ral.cfg_regwen.en] = 0;
    tl_intg_alert_fields[ral.status.sha3_idle] = 0;
    shadow_update_err_status_fields[ral.status.alert_recov_ctrl_update_err] = 1;
    shadow_storage_err_status_fields[ral.status.alert_fatal_fault] = 1;
    shadow_storage_err_status_fields[ral.cfg_regwen.en] = 0;
    shadow_storage_err_status_fields[ral.status.sha3_idle] = 0;

    for (int i = 0; i < kmac_pkg::NumAppIntf; i++) begin
      string name = $sformatf("m_kmac_app_agent_cfg[%0d]", i);
      m_kmac_app_agent_cfg[i] = kmac_app_agent_cfg::type_id::create(name);
      m_kmac_app_agent_cfg[i].if_mode = dv_utils_pkg::Host;
    end
    keymgr_sideload_agent_cfg = key_sideload_agent_cfg#(keymgr_pkg::hw_key_req_t)::type_id
                                ::create("keymgr_sideload_agent_cfg");
    void'($value$plusargs("enable_masking=%0d", enable_masking));
    void'($value$plusargs("sw_key_masked=%0d", sw_key_masked));
    void'($value$plusargs("test_vectors_sha3_variant=%0d", sha3_variant));
    void'($value$plusargs("test_vectors_shake_variant=%0d", shake_variant));

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();

    // only support 1 outstanding TL items in tlul_adapter
    m_tl_agent_cfg.max_outstanding_req = 1;

  endfunction

endclass
