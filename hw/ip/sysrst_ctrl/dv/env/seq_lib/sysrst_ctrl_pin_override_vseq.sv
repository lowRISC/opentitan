// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will optionally override all output signals
// and change the polarity of input and output signals. This
// sequence will verify the pin override module.
class sysrst_ctrl_pin_override_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_pin_override_vseq)

  `uvm_object_new

  rand uvm_reg_data_t en_override, set_value, set_allowed;

  constraint num_trans_c {num_trans == 20;}

  function void perform_checks(input bit en_override_signal,
                               input bit override_val_signal,
                               input bit allowed_1_signal,
                               input bit allowed_0_signal,
                               input bit out_val,
                               input bit in_val);
      if (en_override_signal == 1) begin
        if (override_val_signal == 1 && allowed_1_signal == 1) begin
          `DV_CHECK_EQ(out_val, 1)
        end else if (override_val_signal == 0 && allowed_0_signal == 1) begin
          `DV_CHECK_EQ(out_val, 0)
        end else begin
          `DV_CHECK_EQ(out_val, in_val)
        end
      end else begin
        `DV_CHECK_EQ(out_val, in_val)
      end
  endfunction


  task body();

    uvm_reg_data_t rdata;
    bit en_override_pwrb_out, en_override_key0_out, en_override_key1_out,
        en_override_key2_out, en_override_ec_rst_l_out,
        en_override_bat_disable, en_override_z3_wakeup, en_override_flash_wp;
    bit override_val_pwrb_out, override_val_key0_out, override_val_key1_out,
        override_val_key2_out, override_val_ec_rst_l_out,
        override_val_bat_disable, override_val_z3_wakeup, override_val_flash_wp;
    bit allowed_pwrb_out_0, allowed_key0_out_0, allowed_key1_out_0,
        allowed_key2_out_0, allowed_ec_rst_l_out_0,
        allowed_bat_disable_0, allowed_z3_wakeup_0, allowed_flash_wp_0;
    bit allowed_pwrb_out_1, allowed_key0_out_1, allowed_key1_out_1,
        allowed_key2_out_1, allowed_ec_rst_l_out_1,
        allowed_bat_disable_1, allowed_z3_wakeup_1, allowed_flash_wp_1;

    `uvm_info(`gfn, "Starting the body from pin_override_vseq", UVM_LOW)

    repeat (num_trans) begin

      `DV_CHECK_RANDOMIZE_FATAL(this)

      // Enable the override function
      csr_wr(ral.pin_out_ctl, en_override);

      // Set the pin_override_value
      csr_wr(ral.pin_out_value, set_value);

      // Allow the output values to override
      csr_wr(ral.pin_allowed_ctl, set_allowed);

      // It takes 2-3 clock cycles to sync register values
      cfg.clk_aon_rst_vif.wait_clks(3);

      // Randomize the input pins
      cfg.clk_aon_rst_vif.wait_clks(1);
      cfg.vif.randomize_input();

      csr_rd(ral.pin_out_ctl, rdata);
      en_override_pwrb_out = get_field_val(ral.pin_out_ctl.pwrb_out, rdata);
      en_override_key0_out = get_field_val(ral.pin_out_ctl.key0_out, rdata);
      en_override_key1_out = get_field_val(ral.pin_out_ctl.key1_out, rdata);
      en_override_key2_out = get_field_val(ral.pin_out_ctl.key2_out, rdata);
      en_override_ec_rst_l_out = get_field_val(ral.pin_out_ctl.ec_rst_l, rdata);
      en_override_bat_disable = get_field_val(ral.pin_out_ctl.bat_disable, rdata);
      en_override_z3_wakeup = get_field_val(ral.pin_out_ctl.z3_wakeup, rdata);
      en_override_flash_wp = get_field_val(ral.pin_out_ctl.flash_wp_l, rdata);

      csr_rd(ral.pin_out_value, rdata);
      override_val_pwrb_out = get_field_val(ral.pin_out_value.pwrb_out, rdata);
      override_val_key0_out = get_field_val(ral.pin_out_value.key0_out, rdata);
      override_val_key1_out = get_field_val(ral.pin_out_value.key1_out, rdata);
      override_val_key2_out = get_field_val(ral.pin_out_value.key2_out, rdata);
      override_val_ec_rst_l_out = get_field_val(ral.pin_out_value.ec_rst_l, rdata);
      override_val_bat_disable = get_field_val(ral.pin_out_value.bat_disable, rdata);
      override_val_z3_wakeup = get_field_val(ral.pin_out_value.z3_wakeup, rdata);
      override_val_flash_wp = get_field_val(ral.pin_out_value.flash_wp_l, rdata);

      csr_rd(ral.pin_allowed_ctl, rdata);
      allowed_pwrb_out_0 = get_field_val(ral.pin_allowed_ctl.pwrb_out_0, rdata);
      allowed_key0_out_0 = get_field_val(ral.pin_allowed_ctl.key0_out_0, rdata);
      allowed_key1_out_0 = get_field_val(ral.pin_allowed_ctl.key1_out_0, rdata);
      allowed_key2_out_0 = get_field_val(ral.pin_allowed_ctl.key2_out_0, rdata);
      allowed_bat_disable_0 = get_field_val(ral.pin_allowed_ctl.bat_disable_0, rdata);
      allowed_z3_wakeup_0 = get_field_val(ral.pin_allowed_ctl.z3_wakeup_0, rdata);
      allowed_ec_rst_l_out_0 = get_field_val(ral.pin_allowed_ctl.ec_rst_l_0, rdata);
      allowed_flash_wp_0 = get_field_val(ral.pin_allowed_ctl.flash_wp_l_0, rdata);
      allowed_pwrb_out_1 = get_field_val(ral.pin_allowed_ctl.pwrb_out_1, rdata);
      allowed_key0_out_1 = get_field_val(ral.pin_allowed_ctl.key0_out_1, rdata);
      allowed_key1_out_1 = get_field_val(ral.pin_allowed_ctl.key1_out_1, rdata);
      allowed_key2_out_1 = get_field_val(ral.pin_allowed_ctl.key2_out_1, rdata);
      allowed_ec_rst_l_out_1 = get_field_val(ral.pin_allowed_ctl.ec_rst_l_1, rdata);
      allowed_bat_disable_1 = get_field_val(ral.pin_allowed_ctl.bat_disable_1, rdata);
      allowed_z3_wakeup_1 = get_field_val(ral.pin_allowed_ctl.z3_wakeup_1, rdata);
      allowed_flash_wp_1 = get_field_val(ral.pin_allowed_ctl.flash_wp_l_1, rdata);

      cfg.clk_aon_rst_vif.wait_clks(1);
      perform_checks(en_override_pwrb_out, override_val_pwrb_out, allowed_pwrb_out_1,
          allowed_pwrb_out_0, cfg.vif.pwrb_out, cfg.vif.pwrb_in);

      perform_checks(en_override_key0_out, override_val_key0_out, allowed_key0_out_1,
          allowed_key0_out_0, cfg.vif.key0_out, cfg.vif.key0_in);

      perform_checks(en_override_key1_out, override_val_key1_out, allowed_key1_out_1,
          allowed_key1_out_0, cfg.vif.key1_out, cfg.vif.key1_in);

      perform_checks(en_override_key2_out, override_val_key2_out, allowed_key2_out_1,
          allowed_key2_out_0, cfg.vif.key2_out, cfg.vif.key2_in);

      //ec_rst_l_out is an uninverted output signal
      //ec_rst_l_in has reset value 'h1
      perform_checks(en_override_ec_rst_l_out, override_val_ec_rst_l_out,
          allowed_ec_rst_l_out_1, allowed_ec_rst_l_out_0, cfg.vif.ec_rst_l_out, 0);

      // bat_disable is an output signal and does not have a
      // corresponding input signal so its value will be 0 in else condition
      perform_checks(en_override_bat_disable, override_val_bat_disable,
          allowed_bat_disable_1, allowed_bat_disable_0, cfg.vif.bat_disable, 0);

      // z3_wakeup is an output signal and does not have a
      // corresponding input signal so its value will be 0 in else condition
      perform_checks(en_override_z3_wakeup, override_val_z3_wakeup,
          allowed_z3_wakeup_1, allowed_z3_wakeup_0, cfg.vif.z3_wakeup, 0);

      cov.pin_cfg_cg["bat_disable"].pin_cfg_cg.sample (en_override_bat_disable,
          override_val_bat_disable, allowed_bat_disable_0, allowed_bat_disable_1);

      cov.pin_cfg_cg["ec_rst_l"].pin_cfg_cg.sample (en_override_ec_rst_l_out,
          override_val_ec_rst_l_out, allowed_ec_rst_l_out_0, allowed_ec_rst_l_out_1);

      cov.pin_cfg_cg["pwrb_out"].pin_cfg_cg.sample (en_override_pwrb_out,
          override_val_pwrb_out, allowed_pwrb_out_0, allowed_pwrb_out_1);

      cov.pin_cfg_cg["key0_out"].pin_cfg_cg.sample (en_override_key0_out,
          override_val_key0_out, allowed_key0_out_0, allowed_key0_out_1);

      cov.pin_cfg_cg["key1_out"].pin_cfg_cg.sample (en_override_key1_out,
          override_val_key1_out, allowed_key1_out_0, allowed_key1_out_1);

      cov.pin_cfg_cg["key2_out"].pin_cfg_cg.sample (en_override_key2_out,
          override_val_key2_out, allowed_key2_out_0, allowed_key2_out_1);

      cov.pin_cfg_cg["z3_wakeup"].pin_cfg_cg.sample (en_override_z3_wakeup,
          override_val_z3_wakeup, allowed_z3_wakeup_0, allowed_z3_wakeup_1);

      cov.pin_cfg_cg["flash_wp_l"].pin_cfg_cg.sample (en_override_flash_wp,
          override_val_flash_wp, allowed_flash_wp_0, allowed_flash_wp_1);
    end

  endtask : body

endclass : sysrst_ctrl_pin_override_vseq
