// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_env_cfg extends cip_base_env_cfg #(.RAL_T(ac_range_check_reg_block));

  // Enabling Scoreboard checks downgrading in ac_range_check_scoreboard
  // Addresses issue #27380 that identified in very specific scenarios no valid TLUL transactions
  // will be ever generated
  bit en_scb_err_downgrade;

  // External interfaces
  misc_vif_t misc_vif;

  // External component config objects
  rand tl_agent_cfg tl_unfilt_agt_cfg;
  rand tl_agent_cfg tl_filt_agt_cfg;

  `uvm_object_utils_begin(ac_range_check_env_cfg)
    `uvm_field_object(tl_unfilt_agt_cfg, UVM_DEFAULT)
    `uvm_field_object(tl_filt_agt_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void initialize(bit [31:0] csr_base_addr = '1);
endclass : ac_range_check_env_cfg


function ac_range_check_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void ac_range_check_env_cfg::initialize(bit [31:0] csr_base_addr = '1);
  list_of_alerts = ac_range_check_env_pkg::LIST_OF_ALERTS;
  super.initialize(csr_base_addr);

  // Set shadow register error status
  tl_intg_alert_fields[ral.alert_status.reg_intg_err] = 1;
  shadow_update_err_status_fields[ral.alert_status.shadowed_update_err] = 1;
  shadow_storage_err_status_fields[ral.alert_status.shadowed_storage_err] = 1;

  // TL Agent Configuration objects - Non RAL
  // Create tl_unfilt agent config obj
  tl_unfilt_agt_cfg = tl_agent_cfg::type_id::create("tl_unfilt_agt_cfg");
  tl_unfilt_agt_cfg.if_mode = dv_utils_pkg::Host;

  // Create tl_filt agent config obj
  tl_filt_agt_cfg = tl_agent_cfg::type_id::create("tl_filt_agt_cfg");
  tl_filt_agt_cfg.if_mode = dv_utils_pkg::Device;

  // Set num_interrupts
  begin
    uvm_reg rg = ral.get_reg_by_name("intr_state");
    if (rg != null) begin
      num_interrupts = ral.intr_state.get_n_used_bits();
    end
  end

  // Used to allow reset operations without waiting for CSR accesses to complete
  // At the moment resets will only be used in stress_all_with_rand_reset.
  // Reset strategy in genral will need a rethink (Check PR #25463)
  can_reset_with_csr_accesses = 1;

  // By default no error downgrade is allowed.
  // Only in specific testcases this should be allowed
  en_scb_err_downgrade = 0;
endfunction : initialize
