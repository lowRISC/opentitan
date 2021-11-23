// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will invert the input pins and check the corresponding output and vice versa
class sysrst_ctrl_in_out_inverted_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_in_out_inverted_vseq)

  `uvm_object_new

   uvm_reg_data_t rdata, rdata1;
   bit key0_in_invert, key1_in_invert, key2_in_invert, pwrb_in_invert;
   bit inv_key0_in, inv_key1_in, inv_key2_in, inv_pwrb_in;
   bit key0_out_invert, key1_out_invert, key2_out_invert, pwrb_out_invert;
   bit inv_key0_out, inv_key1_out, inv_key2_out, inv_pwrb_out;
   rand uvm_reg_data_t reg_wrdata;

  constraint num_trans_c {num_trans == 20;}

  task body();
   `uvm_info(`gfn, "Starting the body from in_out_inverted_seq", UVM_LOW)

    // Do not override the reset values of ec_rst_l and flash_wp_l
    csr_wr(ral.pin_out_ctl, 'h0);
    csr_wr(ral.pin_allowed_ctl, 'h0);

    repeat (num_trans) begin

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

    end
  endtask : body

endclass : sysrst_ctrl_in_out_inverted_vseq
