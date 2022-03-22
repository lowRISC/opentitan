// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will verify the flash_wp_l_out signal
// It will be explicitly released from the reset by enabling and
// disabling the override feature. The output, thus will have a transition from
// 1->0 and 0->1
class sysrst_ctrl_flash_wr_prot_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_flash_wr_prot_vseq)

  `uvm_object_new

   rand uvm_reg_data_t en_override_value, set_value, set_allowed;

   constraint num_trans_c {num_trans == 20;}

   task body();

   bit en_override_flash_wp_value, override_val_flash_wp, allowed_flash_wp_0,
       allowed_flash_wp_1;

    `uvm_info(`gfn, "Starting the body from flash_wr_prot_vseq", UVM_LOW)

    repeat (num_trans) begin

      `DV_CHECK_RANDOMIZE_FATAL(this)

      // Enable the override function
      csr_wr(ral.pin_out_ctl, en_override_value);

      // Set the pin_override_value
      csr_wr(ral.pin_out_value, set_value);

      // Allow the output values to override
      csr_wr(ral.pin_allowed_ctl, set_allowed);

      // It takes 2-3 clock cycles to sync register values
      cfg.clk_aon_rst_vif.wait_clks(3);

      // Randomize the input pins
      cfg.clk_aon_rst_vif.wait_clks(1);
      cfg.vif.randomize_input();

      en_override_flash_wp_value = get_field_val(ral.pin_out_ctl.flash_wp_l, en_override_value);

      override_val_flash_wp = get_field_val(ral.pin_out_value.flash_wp_l, set_value);

      allowed_flash_wp_0 = get_field_val(ral.pin_allowed_ctl.flash_wp_l_0, set_allowed);
      allowed_flash_wp_1 = get_field_val(ral.pin_allowed_ctl.flash_wp_l_1, set_allowed);

      cfg.clk_aon_rst_vif.wait_clks(1);
      if (en_override_flash_wp_value == 1) begin
        if (override_val_flash_wp == 1 && allowed_flash_wp_1 == 1) begin
          `DV_CHECK_EQ(cfg.vif.flash_wp_l, 1)
        end else if (override_val_flash_wp == 0 && allowed_flash_wp_0 == 1) begin
          `DV_CHECK_EQ(cfg.vif.flash_wp_l, 0)
        end else begin
          `DV_CHECK_EQ(cfg.vif.flash_wp_l, 0)
        end
      end else begin
        `DV_CHECK_EQ(cfg.vif.flash_wp_l, 0)
      end

    end

     cfg.clk_aon_rst_vif.wait_clks(20);
   endtask : body

endclass : sysrst_ctrl_flash_wr_prot_vseq

