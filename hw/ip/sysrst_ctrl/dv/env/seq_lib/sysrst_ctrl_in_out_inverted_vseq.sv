// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will invert the input pins and check the corresponding output and vice versa
class sysrst_ctrl_in_out_inverted_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_in_out_inverted_vseq)

   uvm_reg_data_t rdata, rdata1;
   bit key0_in_invert, key1_in_invert, key2_in_invert, pwrb_in_invert;
   bit inv_key0_in, inv_key1_in, inv_key2_in, inv_pwrb_in;
   bit key0_out_invert, key1_out_invert, key2_out_invert, pwrb_out_invert;
   bit inv_key0_out, inv_key1_out, inv_key2_out, inv_pwrb_out;
   bit ac_present_invert, bat_disable_invert, lid_open_invert, z3_wakeup_invert;
   rand uvm_reg_data_t reg_wrdata;

  constraint num_trans_c {num_trans == 20;}

  covergroup sysrst_ctrl_key_invert_ctl_cg with function sample (
    bit key0_in,
    bit key0_out,
    bit key1_in,
    bit key1_out,
    bit key2_in,
    bit key2_out,
    bit pwrb_in,
    bit pwrb_out,
    bit ac_present,
    bit bat_disable,
    bit lid_open,
    bit z3_wakeup
  );
    option.per_instance = 1;
    option.name = "sysrst_ctrl_key_invert_ctl_cg";

    cp_key0_in: coverpoint key0_in;
    cp_key0_out: coverpoint key0_out;
    cp_key1_in: coverpoint key1_in;
    cp_key1_out: coverpoint key1_out;
    cp_key2_in: coverpoint key2_in;
    cp_key2_out: coverpoint key2_out;
    cp_pwrb_in: coverpoint pwrb_in;
    cp_pwrb_out: coverpoint pwrb_out;
    cp_ac_present: coverpoint ac_present;
    cp_bat_disable: coverpoint bat_disable;
    cp_lid_open: coverpoint lid_open;
    cp_z3_wakeup: coverpoint z3_wakeup;

    key0_inXval: cross cp_key0_in, cfg.vif.key0_in;
    key0_outXval: cross cp_key0_out, cfg.vif.key0_out;
    key1_inXval: cross cp_key1_in, cfg.vif.key1_in;
    key1_outXval: cross cp_key1_out, cfg.vif.key1_out;
    key2_inXval: cross cp_key2_in, cfg.vif.key2_in;
    key2_outXval: cross cp_key2_out, cfg.vif.key2_out;
    pwrb_inXval: cross cp_pwrb_in, cfg.vif.pwrb_in;
    pwrb_outXval: cross cp_pwrb_out, cfg.vif.pwrb_out;
    ac_presentXval: cross cp_ac_present, cfg.vif.ac_present;
    bat_disableXval: cross cp_bat_disable, cfg.vif.bat_disable {
      ignore_bins invalid0 = binsof(cp_bat_disable) intersect {0} &&
                             binsof(cfg.vif.bat_disable) intersect {1};
      ignore_bins invalid1 = binsof(cp_bat_disable) intersect {1} &&
                             binsof(cfg.vif.bat_disable) intersect {0};
    }
    lid_openXval: cross cp_lid_open, cfg.vif.lid_open;
    z3_wakeupXval: cross cp_z3_wakeup, cfg.vif.z3_wakeup {
      ignore_bins invalid0 = binsof(cp_z3_wakeup) intersect {0} &&
                             binsof(cfg.vif.z3_wakeup) intersect {1};
      ignore_bins invalid1 = binsof(cp_z3_wakeup) intersect {1} &&
                             binsof(cfg.vif.z3_wakeup) intersect {0};
    }

  endgroup // sysrst_ctrl_key_invert_ctl_cg

   function new(string name = "sysrst_ctrl_in_out_inverted_vseq");
    super.new(name);
    sysrst_ctrl_key_invert_ctl_cg = new();
  endfunction : new

  task body();
   `uvm_info(`gfn, "Starting the body from in_out_inverted_seq", UVM_LOW)

    // Do not override the reset values of ec_rst_l and flash_wp_l
    csr_wr(ral.pin_out_ctl, 'h0);
    csr_wr(ral.pin_allowed_ctl, 'h0);

    repeat (num_trans) begin

      `DV_CHECK_RANDOMIZE_FATAL(this)

      // Randomize the input pins
      cfg.vif.randomize_input();

      // Configuring to invert the input pins
      csr_wr(ral.key_invert_ctl, reg_wrdata);

      csr_rd(ral.key_invert_ctl,rdata);

      @(posedge cfg.vif.clk_i)
      key0_in_invert = get_field_val(ral.key_invert_ctl.key0_in, rdata);
      key0_out_invert = get_field_val(ral.key_invert_ctl.key0_out, rdata);
      inv_key0_in = key0_in_invert ? ~cfg.vif.key0_in : cfg.vif.key0_in;
      inv_key0_out = key0_out_invert ? ~cfg.vif.key0_out : cfg.vif.key0_out;
      `DV_CHECK_EQ(inv_key0_in, inv_key0_out)

      key1_in_invert = get_field_val(ral.key_invert_ctl.key1_in, rdata);
      key1_out_invert = get_field_val(ral.key_invert_ctl.key1_out, rdata);
      inv_key1_in = key1_in_invert ? ~cfg.vif.key1_in : cfg.vif.key1_in;
      inv_key1_out = key1_out_invert ? ~cfg.vif.key1_out : cfg.vif.key1_out;
      `DV_CHECK_EQ(inv_key1_in, inv_key1_out)

      key2_in_invert = get_field_val(ral.key_invert_ctl.key2_in, rdata);
      key2_out_invert = get_field_val(ral.key_invert_ctl.key2_out, rdata);
      inv_key2_in = key2_in_invert ? ~cfg.vif.key2_in : cfg.vif.key2_in;
      inv_key2_out = key2_out_invert ? ~cfg.vif.key2_out : cfg.vif.key2_out;
      `DV_CHECK_EQ(inv_key2_in, inv_key2_out)

      pwrb_in_invert = get_field_val(ral.key_invert_ctl.pwrb_in, rdata);
      pwrb_out_invert = get_field_val(ral.key_invert_ctl.pwrb_out, rdata);
      inv_pwrb_in = pwrb_in_invert ? ~cfg.vif.pwrb_in : cfg.vif.pwrb_in;
      inv_pwrb_out = pwrb_out_invert ? ~cfg.vif.pwrb_out : cfg.vif.pwrb_out;
      `DV_CHECK_EQ(inv_pwrb_in, inv_pwrb_out)

      ac_present_invert = get_field_val(ral.key_invert_ctl.ac_present, rdata);
      bat_disable_invert = get_field_val(ral.key_invert_ctl.bat_disable, rdata);
      lid_open_invert = get_field_val(ral.key_invert_ctl.lid_open, rdata);
      z3_wakeup_invert = get_field_val(ral.key_invert_ctl.z3_wakeup, rdata);

      sysrst_ctrl_key_invert_ctl_cg.sample (
        key0_in_invert,
        key0_out_invert,
        key1_in_invert,
        key1_out_invert,
        key2_in_invert,
        key2_out_invert,
        pwrb_in_invert,
        pwrb_out_invert,
        ac_present_invert,
        bat_disable_invert,
        lid_open_invert,
        z3_wakeup_invert
      );

    end
  endtask : body

endclass : sysrst_ctrl_in_out_inverted_vseq
