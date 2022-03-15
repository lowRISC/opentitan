// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// We are enclosing generic covergroups inside class so that we can
// take avoid tool limitation of not allowing arrays of covergroup
// Refer to Issue#375 for more details
//////////////////////////////////////
//  Pin config generic covergroup  ///
//////////////////////////////////////
class sysrst_ctrl_pin_cfgs_obj extends uvm_object;
   `uvm_object_utils(sysrst_ctrl_pin_cfgs_obj)

  covergroup pin_cfg_cg(string name) with function sample (
    bit en_override, bit override_value, bit pin_allowed_0, bit pin_allowed_1
  );
    option.per_instance = 1;
    cp_en_override: coverpoint en_override;
    cp_override_value: coverpoint override_value
      {
        bins from_0to1 = (0 => 1);
        bins from_1to0 = (1 => 0);
      }
    cp_pin_allowed_0: coverpoint pin_allowed_0;
    cp_pin_allowed_1: coverpoint pin_allowed_1;

    // have cross coverpoint if possible
    cp_pin_cross: cross cp_en_override, cp_override_value, cp_pin_allowed_0, cp_pin_allowed_1;
  endgroup : pin_cfg_cg

  // Function new
  function new(string name = "sysrst_ctrl_pin_cfgs_obj");
    super.new(name);
    pin_cfg_cg = new(name);
  endfunction : new
endclass : sysrst_ctrl_pin_cfgs_obj

/////////////////////////////////
// Debounce timer cover points //
/////////////////////////////////
class sysrst_ctrl_debounce_timer_obj extends uvm_object;
   `uvm_object_utils(sysrst_ctrl_debounce_timer_obj)

   covergroup debounce_timer_cg(string name) with function sample (
    bit [15:0] debounce_timer
  );
    option.per_instance = 1;
    cp_debounce_timer: coverpoint debounce_timer
      {
        bins min_range = {[10:50]};
        bins mid_range = {[51:100]};
        bins max_range = {[101:$]};
      }

  endgroup : debounce_timer_cg

  // Function new
  function new(string name = "sysrst_ctrl_debounce_timer_obj");
    super.new(name);
    debounce_timer_cg = new(name);
  endfunction : new
endclass : sysrst_ctrl_debounce_timer_obj

class sysrst_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(sysrst_ctrl_env_cfg)
);

  `uvm_component_utils(sysrst_ctrl_env_cov)

  sysrst_ctrl_pin_cfgs_obj pin_cfg_cg[string];
  sysrst_ctrl_debounce_timer_obj debounce_timer_cg[string];

  function new(string name, uvm_component parent);
    super.new(name, parent);
    pin_cfg_cg["bat_disable"] = new("bat_disable");
    pin_cfg_cg["ec_rst_l"] = new("ec_rst_l");
    pin_cfg_cg["pwrb_out"] = new("pwrb_out");
    pin_cfg_cg["key0_out"] = new("key0_out");
    pin_cfg_cg["key1_out"] = new("key1_out");
    pin_cfg_cg["key2_out"] = new("key2_out");
    pin_cfg_cg["z3_wakeup"] = new("z3_wakeup");
    pin_cfg_cg["flash_wp_l"] = new("flash_wp_l");

    debounce_timer_cg["ec_rst_ctl"] = new("ec_rst_ctl");
    debounce_timer_cg["key_intr_debounce_ctl"] = new("key_intr_debounce_ctl");
    debounce_timer_cg["ulp_ac_debounce_ctl"] = new("ulp_ac_debounce_ctl");
    debounce_timer_cg["ulp_pwrb_debounce_ctl"] = new("ulp_pwrb_debounce_ctl");
    debounce_timer_cg["ulp_lid_debounce_ctl"] = new("ulp_lid_debounce_ctl");
  endfunction : new

endclass

