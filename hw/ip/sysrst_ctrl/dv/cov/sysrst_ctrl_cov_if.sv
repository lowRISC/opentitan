// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for SYSRST_CTRL

interface sysrst_ctrl_cov_if
  (
   input logic   clk_i,
   input logic   rst_ni
  );

  import uvm_pkg::*;
  import sysrst_ctrl_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  /////////////////////////////////////////////////
  // Combo detection timer register cover points //
  /////////////////////////////////////////////////

  covergroup sysrst_ctrl_combo_detect_det_cg (int index) with function sample (
    bit [31:0] detection_timer
  );
    option.per_instance = 1;
    option.name = $sformatf("sysrst_ctrl_combo_detect_det_cg_%0d", index);

    cp_detect_timer: coverpoint detection_timer
      {
        bins min_range = {[10:50]};
        bins mid_range = {[51:100]};
        bins max_range = {[101:$]};
      }
  endgroup // sysrst_ctrl_combo_detect_det_cg

  ///////////////////////////////////////////////////////
  // Auto block debounce control register cover points //
  ///////////////////////////////////////////////////////

  covergroup sysrst_ctrl_auto_block_debounce_ctl_cg with function sample (
    bit [15:0] debounce_timer,
    bit auto_block_enable
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_auto_block_debounce_ctl_cg";

    cp_auto_block_enable: coverpoint auto_block_enable;
    cp_debounce_timer: coverpoint debounce_timer
      {
        bins min_range = {[10:50]};
        bins mid_range = {[51:100]};
        bins max_range = {[101:$]};
      }

  endgroup // sysrst_ctrl_auto_block_debounce_ctl_cg

  /////////////////////////////////////////////
  // key intr status register cover points //
  /////////////////////////////////////////////

  covergroup sysrst_ctrl_key_intr_status_cg with function sample (
    bit pwrb_h2l,
    bit key0_in_h2l,
    bit key1_in_h2l,
    bit key2_in_h2l,
    bit ac_present_h2l,
    bit ec_rst_l_h2l,
    bit flash_wp_l_h2l,
    bit pwrb_l2h,
    bit key0_in_l2h,
    bit key1_in_l2h,
    bit key2_in_l2h,
    bit ac_present_l2h,
    bit ec_rst_l_l2h,
    bit flash_wp_l_l2h
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_key_intr_status_cg";

    cp_pwrb_h2l: coverpoint pwrb_h2l;
    cp_key0_in_h2l: coverpoint key0_in_h2l;
    cp_key1_in_h2l: coverpoint key1_in_h2l;
    cp_key2_in_h2l: coverpoint key2_in_h2l;
    cp_ac_present_h2l: coverpoint ac_present_h2l;
    cp_ec_rst_l_h2l: coverpoint ec_rst_l_h2l;
    cp_flash_wp_l_h2l: coverpoint flash_wp_l_h2l;
    cp_pwrb_l2h: coverpoint pwrb_l2h;
    cp_key0_in_l2h: coverpoint key0_in_l2h;
    cp_key1_in_l2h: coverpoint key1_in_l2h;
    cp_key2_in_l2h: coverpoint key2_in_l2h;
    cp_ac_present_l2h: coverpoint ac_present_l2h;
    cp_ec_rst_l_l2h: coverpoint ec_rst_l_l2h;
    cp_flash_wp_l_l2h: coverpoint flash_wp_l_l2h;

  endgroup // sysrst_ctrl_key_intr_status_cg

  ///////////////////////////////
  // Wakeup event cover points //
  ///////////////////////////////

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
        ignore_bins invalid = binsof(cp_h2l_pwrb) intersect {1} &&
                            binsof(cp_l2h_lid_open) intersect {0} &&
                            binsof(cp_h_ac_present) intersect {0} &&
                            binsof(cp_wakeup_sts) intersect {0} &&
                            binsof(cp_interrupt_gen) intersect {0};
      }
  endgroup // sysrst_ctrl_wkup_event_cg

  //////////////////////////////////////
  // Pin in value register cover points //
  //////////////////////////////////////
  covergroup sysrst_ctrl_pin_in_value_cg with function sample (
    bit pwrb_in,
    bit key0_in,
    bit key1_in,
    bit key2_in,
    bit lid_open,
    bit ac_present,
    bit ec_rst_l,
    bit flash_wp_l
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_pin_in_value_cg";

    cp_pwrb_in: coverpoint pwrb_in;
    cp_key0_in: coverpoint key0_in;
    cp_key1_in: coverpoint key1_in;
    cp_key2_in: coverpoint key2_in;
    cp_lid_open: coverpoint lid_open;
    cp_ac_present: coverpoint ac_present;
    cp_ec_rst_l: coverpoint ec_rst_l;
    cp_flash_wp_l: coverpoint flash_wp_l;

  endgroup // sysrst_ctrl_pin_in_value_cg

  ///////////////////////////////////
  // Instantiation Macros          //
  ///////////////////////////////////
  `DV_FCOV_INSTANTIATE_CG(sysrst_ctrl_auto_block_debounce_ctl_cg)
  `DV_FCOV_INSTANTIATE_CG(sysrst_ctrl_key_intr_status_cg)
  `DV_FCOV_INSTANTIATE_CG(sysrst_ctrl_wkup_event_cg)
  `DV_FCOV_INSTANTIATE_CG(sysrst_ctrl_pin_in_value_cg)

  sysrst_ctrl_combo_detect_det_cg combo_detect_det_cg_inst[4];
  initial begin
    foreach (combo_detect_det_cg_inst[i]) begin
      combo_detect_det_cg_inst[i] = new(i);
    end
  end

  /////////////////////
  // Sample function //
  /////////////////////
  function automatic void cg_combo_detect_det_sample(
    int index,
    bit [31:0] detection_timer
  );
    foreach (combo_detect_det_cg_inst[i]) begin
      combo_detect_det_cg_inst[index].sample(detection_timer);
    end
  endfunction

  function automatic void cg_auto_block_sample (
    bit [15:0] debounce_timer,
    bit auto_block_enable
  );
    sysrst_ctrl_auto_block_debounce_ctl_cg_inst.sample(debounce_timer, auto_block_enable);
  endfunction

  function automatic void cg_key_intr_status_sample (
    bit pwrb_h2l,
    bit key0_in_h2l,
    bit key1_in_h2l,
    bit key2_in_h2l,
    bit ac_present_h2l,
    bit ec_rst_l_h2l,
    bit flash_wp_l_h2l,
    bit pwrb_l2h,
    bit key0_in_l2h,
    bit key1_in_l2h,
    bit key2_in_l2h,
    bit ac_present_l2h,
    bit ec_rst_l_l2h,
    bit flash_wp_l_l2h
  );
    sysrst_ctrl_key_intr_status_cg_inst.sample(pwrb_h2l, key0_in_h2l, key1_in_h2l, key2_in_h2l,
           ac_present_h2l, ec_rst_l_h2l, flash_wp_l_h2l, pwrb_l2h, key0_in_l2h, key1_in_l2h,
           key2_in_l2h, ac_present_l2h, ec_rst_l_l2h, flash_wp_l_l2h);
  endfunction

  function automatic void cg_wkup_event_sample (
    bit wakeup_sts,
    bit h2l_pwrb,
    bit l2h_lid_open,
    bit h_ac_present,
    bit interrupt_gen
  );
    sysrst_ctrl_wkup_event_cg_inst.sample(wakeup_sts, h2l_pwrb, l2h_lid_open, h_ac_present,
       interrupt_gen);
  endfunction

  function automatic void cg_pin_in_value_sample (
    bit pwrb_in,
    bit key0_in,
    bit key1_in,
    bit key2_in,
    bit lid_open,
    bit ac_present,
    bit ec_rst_l,
    bit flash_wp_l
  );
    sysrst_ctrl_pin_in_value_cg_inst.sample (pwrb_in, key0_in,
        key1_in, key2_in, lid_open, ac_present, ec_rst_l, flash_wp_l);
  endfunction

endinterface
