// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will read the raw input pins values.
class sysrst_ctrl_pin_access_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_pin_access_vseq)

  `uvm_object_new

   uvm_reg_data_t rdata;

   task body();
      bit rdata_pwrb_in, rdata_key0_in, rdata_key1_in, rdata_key2_in,
          rdata_ec_rst_l_in, rdata_flash_wp_l_in, rdata_ac_present, rdata_lid_open;

      `uvm_info(`gfn, "Starting the body from pin_access_vseq", UVM_LOW)

      repeat ($urandom_range(1,50)) begin
        // Randomize the input pins
        cfg.vif.randomize_input();

        // Read the raw input pin values
        cfg.clk_aon_rst_vif.wait_clks(1);
        csr_rd(ral.pin_in_value, rdata);
        rdata_pwrb_in = get_field_val(ral.pin_in_value.pwrb_in, rdata);
        rdata_key0_in = get_field_val(ral.pin_in_value.key0_in, rdata);
        rdata_key1_in = get_field_val(ral.pin_in_value.key1_in, rdata);
        rdata_key2_in = get_field_val(ral.pin_in_value.key2_in, rdata);
        rdata_ec_rst_l_in = get_field_val(ral.pin_in_value.ec_rst_l, rdata);
        rdata_flash_wp_l_in = get_field_val(ral.pin_in_value.flash_wp_l, rdata);
        rdata_ac_present = get_field_val(ral.pin_in_value.ac_present, rdata);
        rdata_lid_open = get_field_val(ral.pin_in_value.lid_open, rdata);

        `DV_CHECK_EQ(cfg.vif.pwrb_in, rdata_pwrb_in)
        `DV_CHECK_EQ(cfg.vif.key0_in, rdata_key0_in)
        `DV_CHECK_EQ(cfg.vif.key1_in, rdata_key1_in)
        `DV_CHECK_EQ(cfg.vif.key2_in, rdata_key2_in)
        `DV_CHECK_EQ(cfg.vif.ec_rst_l_in, rdata_ec_rst_l_in)
        `DV_CHECK_EQ(cfg.vif.flash_wp_l_in, rdata_flash_wp_l_in)
        `DV_CHECK_EQ(cfg.vif.ac_present, rdata_ac_present)
        `DV_CHECK_EQ(cfg.vif.lid_open, rdata_lid_open)

      end
   endtask : body

endclass : sysrst_ctrl_pin_access_vseq
