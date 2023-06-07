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

////////////////////////////////////////////////
// Combo detect actions register cover points //
////////////////////////////////////////////////
class sysrst_ctrl_combo_detect_action_obj extends uvm_object;
   `uvm_object_utils(sysrst_ctrl_combo_detect_action_obj)

  covergroup sysrst_ctrl_combo_detect_action_cg (int index) with function sample (
    bit bat_disable,
    bit interrupt,
    bit ec_rst,
    bit rst_req,
    bit key0_in_sel,
    bit key1_in_sel,
    bit key2_in_sel,
    bit pwrb_in_sel,
    bit ac_present_sel,
    bit precondition_key0_in_sel,
    bit precondition_key1_in_sel,
    bit precondition_key2_in_sel,
    bit precondition_pwrb_in_sel,
    bit precondition_ac_present_sel
  );
    option.per_instance = 1;
    option.name = $sformatf("sysrst_ctrl_combo_detect_action_cg_%0d", index);

    cp_bat_disable:    coverpoint bat_disable;
    cp_interrupt:      coverpoint interrupt;
    cp_ec_rst:         coverpoint ec_rst;
    cp_rst_req:        coverpoint rst_req;
    cp_key0_in_sel:    coverpoint key0_in_sel;
    cp_key1_in_sel:    coverpoint key1_in_sel;
    cp_key2_in_sel:    coverpoint key2_in_sel;
    cp_pwrb_in_sel:    coverpoint pwrb_in_sel;
    cp_ac_present_sel: coverpoint ac_present_sel;
    cp_precondition_key0_in_sel:    coverpoint precondition_key0_in_sel;
    cp_precondition_key1_in_sel:    coverpoint precondition_key1_in_sel;
    cp_precondition_key2_in_sel:    coverpoint precondition_key2_in_sel;
    cp_precondition_pwrb_in_sel:    coverpoint precondition_pwrb_in_sel;
    cp_precondition_ac_present_sel: coverpoint precondition_ac_present_sel;
  endgroup  // sysrst_ctrl_combo_detect_action_cg

  function new(string name = "sysrst_ctrl_combo_detect_action_obj");
    string str_idx;
    super.new(name);
    // Get index from argument
    str_idx = name.substr(name.len - 1, name.len - 1);
    sysrst_ctrl_combo_detect_action_cg = new(str_idx.atoi());
  endfunction : new
endclass : sysrst_ctrl_combo_detect_action_obj

////////////////////////////////////////////////
// Combo detect key combinations cover points //
// Because there are many key combinations    //
// and each combo block is the same we can    //
// aggregate these statistics.                //
////////////////////////////////////////////////
class sysrst_ctrl_combo_key_combinations_obj extends uvm_object;
  `uvm_object_utils(sysrst_ctrl_combo_key_combinations_obj)

  covergroup sysrst_ctrl_combo_key_combinations_cg with function sample (
    bit bat_disable,
    bit interrupt,
    bit ec_rst,
    bit rst_req,
    bit key0_in_sel,
    bit key1_in_sel,
    bit key2_in_sel,
    bit pwrb_in_sel,
    bit ac_present_sel,
    bit precondition_key0_in_sel,
    bit precondition_key1_in_sel,
    bit precondition_key2_in_sel,
    bit precondition_pwrb_in_sel,
    bit precondition_ac_present_sel
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_combo_key_combinations_cg";

    cp_key0_in_sel:    coverpoint key0_in_sel;
    cp_key1_in_sel:    coverpoint key1_in_sel;
    cp_key2_in_sel:    coverpoint key2_in_sel;
    cp_pwrb_in_sel:    coverpoint pwrb_in_sel;
    cp_ac_present_sel: coverpoint ac_present_sel;
    cp_precondition_key0_in_sel:    coverpoint precondition_key0_in_sel;
    cp_precondition_key1_in_sel:    coverpoint precondition_key1_in_sel;
    cp_precondition_key2_in_sel:    coverpoint precondition_key2_in_sel;
    cp_precondition_pwrb_in_sel:    coverpoint precondition_pwrb_in_sel;
    cp_precondition_ac_present_sel: coverpoint precondition_ac_present_sel;

    cross_key_combinations_combo_precondition_sel: cross cp_precondition_key0_in_sel,
      cp_precondition_key1_in_sel, cp_precondition_key2_in_sel, cp_precondition_pwrb_in_sel,
      cp_precondition_ac_present_sel iff ((bat_disable || interrupt || ec_rst || rst_req) &&
      (key0_in_sel || key1_in_sel || key2_in_sel || pwrb_in_sel || ac_present_sel)) {
      // Ignore case where all keys are enabled for precondition, as there wont be any keys left for
      // combo detection
      ignore_bins detection_disable = binsof(cp_precondition_key0_in_sel)    intersect {1} &&
                                      binsof(cp_precondition_key1_in_sel)    intersect {1} &&
                                      binsof(cp_precondition_key2_in_sel)    intersect {1} &&
                                      binsof(cp_precondition_pwrb_in_sel)    intersect {1} &&
                                      binsof(cp_precondition_ac_present_sel) intersect {1};
    }

    cross_key_combinations_combo_detection_sel: cross cp_key0_in_sel, cp_key1_in_sel,
      cp_key2_in_sel, cp_pwrb_in_sel, cp_ac_present_sel
      iff (bat_disable || interrupt || ec_rst || rst_req) {
      ignore_bins detection_disable = binsof(cp_key0_in_sel)    intersect {0} &&
                                      binsof(cp_key1_in_sel)    intersect {0} &&
                                      binsof(cp_key2_in_sel)    intersect {0} &&
                                      binsof(cp_pwrb_in_sel)    intersect {0} &&
                                      binsof(cp_ac_present_sel) intersect {0};
    }
  endgroup  // sysrst_ctrl_combo_key_combinations_cg

  function new(string name = "sysrst_ctrl_combo_key_combinations_obj");
    super.new(name);
    sysrst_ctrl_combo_key_combinations_cg = new();
  endfunction : new
endclass : sysrst_ctrl_combo_key_combinations_obj

/////////////////////////////////////////////
// Combo intr status register cover points //
/////////////////////////////////////////////
class sysrst_ctrl_combo_intr_status_obj extends uvm_object;
   `uvm_object_utils(sysrst_ctrl_combo_intr_status_obj)

  covergroup sysrst_ctrl_combo_intr_status_cg with function sample (
    bit combo0_h2l,
    bit combo1_h2l,
    bit combo2_h2l,
    bit combo3_h2l,
    bit key0_in_sel,
    bit key1_in_sel,
    bit key2_in_sel,
    bit pwrb_in_sel,
    bit ac_present_sel,
    bit interrupt
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_combo_intr_status_cg";

    cp_combo0_h2l: coverpoint combo0_h2l;
    cp_combo1_h2l: coverpoint combo1_h2l;
    cp_combo2_h2l: coverpoint combo2_h2l;
    cp_combo3_h2l: coverpoint combo3_h2l;
    cp_key0_in_sel:   coverpoint key0_in_sel;
    cp_key1_in_sel:   coverpoint key1_in_sel;
    cp_key2_in_sel:   coverpoint key2_in_sel;
    cp_pwrb_in_sel:   coverpoint pwrb_in_sel;
    cp_ac_present_sel:coverpoint ac_present_sel;
    cp_interrupt:   coverpoint interrupt;
    cross_combo0: cross cp_combo0_h2l, cp_key0_in_sel, cp_key1_in_sel, cp_key2_in_sel,
      cp_pwrb_in_sel, cp_ac_present_sel, cp_interrupt {
      ignore_bins invalid0 = binsof(cp_interrupt) intersect {0} &&
                             binsof(cp_combo0_h2l) intersect {1};
      }
    cross_combo1: cross cp_combo1_h2l, cp_key0_in_sel, cp_key1_in_sel, cp_key2_in_sel,
      cp_pwrb_in_sel, cp_ac_present_sel, cp_interrupt {
      ignore_bins invalid0 = binsof(cp_interrupt) intersect {0} &&
                             binsof(cp_combo1_h2l) intersect {1};
      }
    cross_combo2: cross cp_combo2_h2l, cp_key0_in_sel, cp_key1_in_sel, cp_key2_in_sel,
      cp_pwrb_in_sel, cp_ac_present_sel, cp_interrupt {
      ignore_bins invalid0 = binsof(cp_interrupt) intersect {0} &&
                             binsof(cp_combo2_h2l) intersect {1};
      }
    cross_combo3: cross cp_combo3_h2l, cp_key0_in_sel, cp_key1_in_sel, cp_key2_in_sel,
      cp_pwrb_in_sel, cp_ac_present_sel, cp_interrupt {
      ignore_bins invalid0 = binsof(cp_interrupt) intersect {0} &&
                             binsof(cp_combo3_h2l) intersect {1};
      }
  endgroup // sysrst_ctrl_combo_intr_status_cg

  function new(string name = "sysrst_ctrl_combo_intr_status_obj");
    super.new(name);
    sysrst_ctrl_combo_intr_status_cg = new();
  endfunction : new
endclass : sysrst_ctrl_combo_intr_status_obj

///////////////////////////////
// Wakeup event cover points //
///////////////////////////////
class sysrst_ctrl_wakeup_event_obj extends uvm_object;
   `uvm_object_utils(sysrst_ctrl_wakeup_event_obj)

  covergroup sysrst_ctrl_wkup_event_cg with function sample (
    bit wakeup_sts,
    bit h2l_pwrb,
    bit l2h_lid_open,
    bit h_ac_present,
    bit interrupt_gen
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_wkup_event_cg";

    cp_wakeup_sts: coverpoint wakeup_sts;
    cp_h2l_pwrb: coverpoint h2l_pwrb;
    cp_l2h_lid_open: coverpoint l2h_lid_open;
    cp_h_ac_present: coverpoint h_ac_present;
    cp_interrupt_gen: coverpoint interrupt_gen;
    cross_wkup_sts: cross cp_wakeup_sts, cp_h2l_pwrb, cp_l2h_lid_open, cp_h_ac_present,
      cp_interrupt_gen {
        ignore_bins invalid0 = binsof(cp_h2l_pwrb) intersect {1} &&
                            binsof(cp_l2h_lid_open) intersect {0} &&
                            binsof(cp_h_ac_present) intersect {0} &&
                            binsof(cp_wakeup_sts) intersect {1} &&
                            binsof(cp_interrupt_gen) intersect {0};
        ignore_bins invalid1 = binsof(cp_interrupt_gen) intersect {1} &&
                               binsof(cp_wakeup_sts) intersect {0};
      }
  endgroup // sysrst_ctrl_wkup_event_cg

  // Function new
  function new(string name = "sysrst_ctrl_wakeup_event_obj");
    super.new(name);
    sysrst_ctrl_wkup_event_cg = new();
  endfunction : new
endclass : sysrst_ctrl_wakeup_event_obj

class sysrst_ctrl_env_cov extends cip_base_env_cov #(
  .CFG_T(sysrst_ctrl_env_cfg)
);

  `uvm_component_utils(sysrst_ctrl_env_cov)

  sysrst_ctrl_pin_cfgs_obj pin_cfg_cg[string];
  sysrst_ctrl_debounce_timer_obj debounce_timer_cg[string];
  sysrst_ctrl_combo_detect_action_obj combo_detect_action[int];
  sysrst_ctrl_combo_key_combinations_obj combo_key_combinations;
  sysrst_ctrl_combo_intr_status_obj combo_intr_status;
  sysrst_ctrl_wakeup_event_obj wakeup_event;

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

    for (int i = 0; i <= 3; i++) begin
      combo_detect_action[i] = new($sformatf("sysrst_ctrl_combo_detect_action_obj_%0d",i));
    end

    combo_key_combinations = new();
    combo_intr_status = new();
    wakeup_event = new();
  endfunction : new

endclass
