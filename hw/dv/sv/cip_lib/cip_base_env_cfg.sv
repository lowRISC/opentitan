// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_env_cfg #(type RAL_T = dv_base_reg_block) extends dv_base_env_cfg #(RAL_T);
  // control knobs to enable/disable covergroups
  // these are default enabled. If en_cov is off, these will be disabled as well.
  bit en_tl_err_cov      = 1;
  bit en_tl_intg_err_cov = 1;

  // Downstream agent cfg objects.

  // If the block supports only one RAL, just use `m_tl_agent_cfg`.
  // If there are multiple RALs, `m_tl_agent_cfg` is the default one for RAL with type `RAL_T`.
  // For the other RAL, can get from ral_models[string] and agent cfg from m_tl_agent_cfgs[string].
  tl_agent_cfg        m_tl_agent_cfg;
  rand tl_agent_cfg   m_tl_agent_cfgs[string];

  // Override this alert name at `initialize` if it's not as below.
  string              tl_intg_alert_name = "fatal_fault";
  string              sec_cm_alert_name  = "fatal_fault";

  // If there is a bit in an "alert cause" register that will be set by a corrupt bus access, this
  // should be the name of that field (with syntax "reg.field"). Used by cip_base_scoreboard to
  // update the relevant field in the RAL model if it sees an error.
  // Format: tl_intg_alert_fields[ral.a_reg.a_field] = value
  uvm_reg_data_t      tl_intg_alert_fields[dv_base_reg_field];

  // Flag to indicate tl mem acess are gated due to local or global escalation.
  bit                 tl_mem_access_gated;

  // Flag to indicate if it is an IP or chip level testbench.
  bit                 is_chip;

  // Similar to the associative array above, if DUT has shadow registers, these two associative
  // arrays contains register fields related to shadow register's update and storage error status.
  uvm_reg_data_t      shadow_update_err_status_fields[dv_base_reg_field];
  uvm_reg_data_t      shadow_storage_err_status_fields[dv_base_reg_field];

  alert_esc_agent_cfg m_alert_agent_cfgs[string];
  push_pull_agent_cfg#(.DeviceDataWidth(EDN_DATA_WIDTH)) m_edn_pull_agent_cfgs[];

  // EDN clk freq setting, if EDN is present.
  rand uint edn_clk_freq_mhz;
  rand clk_freq_diff_e tlul_and_edn_clk_freq_diff;

  // Common interfaces - interrupts, alerts, edn clk.
  intr_vif            intr_vif;
  rst_shadowed_vif    rst_shadowed_vif;
  virtual clk_rst_if  edn_clk_rst_vif;

  // If the data intg is passthru for the memory and the data intg value in mem is incorrect, it
  // won't trigger d_error in this mem block and the check is done in the processor
  // User can set this flag to disable the check for d_user.data_intg
  bit disable_d_user_data_intg_check_for_passthru_mem;

  // Clone the default_map to jtag_riscv_map via adding `run_opts: ["create_jtag_riscv_map=1"]`.
  // After setting this flag, please do not forget to set the correct sequencer to this map,
  // and if needed, set the map as default_map.
  uvm_reg_map jtag_riscv_map;

  uint num_interrupts;
  uint num_edn;

  // Knob to disable random delays in specific `prim_cdc_rand_delay`s even if CDC instrumentation is
  // generally enabled.  This takes one absolute path to a `prim_cdc_rand_delay` instance per array
  // element.
  //
  // This can be used to disable CDC instrumentation specifically for `prim_alert_sender`s, for
  // which the scoreboard -- if random CDC delays were enabled -- would not know precisely in which
  // clock cycle the handshake for an alert completes and thus could not accurately predict whether
  // an alert request gets merged with an outstanding request or not (#18796).
  string disabled_prim_cdc_rand_delays[];

  // if module has alerts, this list_of_alerts needs to override in cfg before super.initialize()
  // function is called
  string list_of_alerts[] = {};

  constraint edn_clk_freq_mhz_c {
    solve tlul_and_edn_clk_freq_diff before edn_clk_freq_mhz;

    if (tlul_and_edn_clk_freq_diff == ClkFreqDiffNone) {
      edn_clk_freq_mhz == clk_freq_mhz;
    } else if (tlul_and_edn_clk_freq_diff == ClkFreqDiffSmall) {
      edn_clk_freq_mhz != clk_freq_mhz;
      // This could have used a function, but per the LRM that could cause circular
      // constraints against the "solve ... before" above. Same thing below for the
      // "big" setting.
      // cast to `int`, as edn_clk_freq_mhz and clk_freq_mhz are unsigned.
      int'(edn_clk_freq_mhz - clk_freq_mhz) inside {[-2 : 2]};
    } else if (tlul_and_edn_clk_freq_diff == ClkFreqDiffBig) {
      // max diff is 100-24=76
      !(int'(edn_clk_freq_mhz - clk_freq_mhz) inside {[-70 : 70]});
    }

    `DV_COMMON_CLK_CONSTRAINT(edn_clk_freq_mhz)
  }
  `uvm_object_param_utils_begin(cip_base_env_cfg #(RAL_T))
    `uvm_field_aa_object_string(m_tl_agent_cfgs,   UVM_DEFAULT)
    `uvm_field_aa_object_string(m_alert_agent_cfgs, UVM_DEFAULT)
    `uvm_field_int             (num_interrupts,    UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [BUS_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // Create downstream agent cfg objects.
    foreach (ral_model_names[i]) begin
      string ral_name = ral_model_names[i];

      m_tl_agent_cfgs[ral_name] = tl_agent_cfg::type_id::create({"m_tl_agent_cfg_", ral_name});
      m_tl_agent_cfgs[ral_name].if_mode = dv_utils_pkg::Host;
      // TL host cannot support device same cycle response. Host may drive d_ready=0 when a_valid=1.
      m_tl_agent_cfgs[ral_name].host_can_stall_rsp_when_a_valid_high = $urandom_range(0, 1);

      // OpenTitan host should hold a_valid high until receiving a_ready, but it's valid behavior
      // to drop a_valid without a_ready
      // randomize `allow_a_valid_drop_wo_a_ready` to test TL device can support it
      m_tl_agent_cfgs[ral_name].allow_a_valid_drop_wo_a_ready = $urandom_range(0, 1);
    end

    // Assign handle to the default `m_tl_agent_cfg` for default `RAL_T`
    if (ral_model_names.size > 0) begin
      `DV_CHECK_FATAL(m_tl_agent_cfgs.exists(RAL_T::type_name))
      m_tl_agent_cfg = m_tl_agent_cfgs[RAL_T::type_name];
      `DV_CHECK_NE_FATAL(m_tl_agent_cfg, null)
    end

    check_shadow_reg_alerts();
    if (list_of_alerts.size() > 0) begin
      check_alert_configs();
      foreach(list_of_alerts[i]) begin
        string alert_name = list_of_alerts[i];
        m_alert_agent_cfgs[alert_name] = alert_esc_agent_cfg::type_id::create(
            $sformatf("m_alert_agent_cfgs[%s]", alert_name));
        `DV_CHECK_RANDOMIZE_FATAL(m_alert_agent_cfgs[alert_name])
        m_alert_agent_cfgs[alert_name].if_mode = dv_utils_pkg::Device;
        m_alert_agent_cfgs[alert_name].is_async = 1; // default async_on, can override this
        m_alert_agent_cfgs[alert_name].en_ping_cov = 0;
        m_alert_agent_cfgs[alert_name].en_lpg_cov = 0;
      end
    end

    m_edn_pull_agent_cfgs = new[num_edn];
    foreach (m_edn_pull_agent_cfgs[i]) begin
      m_edn_pull_agent_cfgs[i] = push_pull_agent_cfg#(.DeviceDataWidth(EDN_DATA_WIDTH))::type_id::
                                 create("m_edn_pull_agent_cfgs");
      `DV_CHECK_RANDOMIZE_FATAL(m_edn_pull_agent_cfgs[i])
      m_edn_pull_agent_cfgs[i].agent_type = PullAgent;
      m_edn_pull_agent_cfgs[i].if_mode    = Device;
      m_edn_pull_agent_cfgs[i].hold_d_data_until_next_req = 1;
    end

    if (jtag_riscv_map != null) ral.set_base_addr(ral.default_map.get_base_addr(), jtag_riscv_map);
  endfunction

  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
    // Usually plusargs are collected during build_phase, but need this variable here during RAL
    // initialization.
    bit create_jtag_riscv_map;
    void'($value$plusargs("create_jtag_riscv_map=%0b", create_jtag_riscv_map));
    if (create_jtag_riscv_map) begin
      jtag_riscv_map = clone_reg_map("jtag_riscv_map", ral.default_map);
      `uvm_info(`gfn, "Cloned default_map to jtag_riscv_map.", UVM_HIGH)
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
  // - Note that shadow alerts originating inside the alert_handler are not checked here
  //   since these are wired up as "local" alerts within the alert_handler.
  virtual function void check_shadow_reg_alerts();
    dv_base_reg shadowed_csrs[$];
    string update_err_alert_name, storage_err_alert_name;

    foreach (ral_models[i]) ral_models[i].get_shadowed_regs(shadowed_csrs);
    foreach (shadowed_csrs[i]) begin
      update_err_alert_name = shadowed_csrs[i].get_update_err_alert_name();
      storage_err_alert_name = shadowed_csrs[i].get_storage_err_alert_name();

      if (update_err_alert_name == "" || storage_err_alert_name == "") begin
        `uvm_fatal(shadowed_csrs[i].get_full_name,
                   "please add update_err and storage_err alert names in Hjson!")
      end

      // check if alert names are valid
      if (!(update_err_alert_name inside {list_of_alerts} ||
          update_err_alert_name == "alert_handler_")) begin
        `uvm_fatal(shadowed_csrs[i].get_full_name, $sformatf(
                   "update_err alert name %0s not in list_of_alerts", update_err_alert_name))
      end
      if (!(storage_err_alert_name inside {list_of_alerts} ||
          storage_err_alert_name == "alert_handler_")) begin
        `uvm_fatal(shadowed_csrs[i].get_full_name, $sformatf(
                   "storage_err alert name %0s not in list_of_alerts", storage_err_alert_name))
      end
    end

  endfunction

 endclass
