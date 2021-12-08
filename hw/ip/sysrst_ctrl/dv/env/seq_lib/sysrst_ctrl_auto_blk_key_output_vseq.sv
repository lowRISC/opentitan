// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will enable the auto block feature and will override
// the key output with their override values set in auto_block_out_ctl reg
class sysrst_ctrl_auto_blk_key_output_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_auto_blk_key_output_vseq)

  `uvm_object_new

   rand uvm_reg_data_t set_timer, override_value;

   constraint set_timer_c {set_timer <= 16'hffff;}

   constraint num_trans_c {num_trans == 3;}

   task body();

    uvm_reg_data_t rdata;
    bit enable_key0_out_sel, enable_key1_out_sel, enable_key2_out_sel;
    bit override_key0_out_value, override_key1_out_value, override_key2_out_value;

    `uvm_info(`gfn, "Starting the body from auto_blk_key_output_vseq", UVM_LOW)

    repeat (num_trans) begin
      // Enable the auto block key feature
      ral.auto_block_debounce_ctl.auto_block_enable.set(1);
      csr_update(ral.auto_block_debounce_ctl);

      // Set the auto block debounce timer value
      csr_wr(ral.auto_block_debounce_ctl.debounce_timer, set_timer);
      `uvm_info(`gfn, $sformatf("Debounce timer set for: %0h",set_timer), UVM_LOW)

      // Set the key outputs to auto override with their values
      csr_wr(ral.auto_block_out_ctl, override_value);

      // It takes 2-3 clock cycles to sync the register values
      cfg.clk_aon_rst_vif.wait_clks(3);

      repeat ($urandom_range(1,5)) begin
       // Press the pwrb_in input key
       cfg.clk_aon_rst_vif.wait_clks(1);
       cfg.vif.randomize_input();
      end

      // Wait for the timer to reach the value configured to debounce_timer
      cfg.clk_aon_rst_vif.wait_clks(set_timer);

      csr_rd(ral.auto_block_out_ctl, rdata);

      enable_key0_out_sel = get_field_val(ral.auto_block_out_ctl.key0_out_sel, rdata);
      enable_key1_out_sel = get_field_val(ral.auto_block_out_ctl.key1_out_sel, rdata);
      enable_key2_out_sel = get_field_val(ral.auto_block_out_ctl.key2_out_sel, rdata);

      override_key0_out_value = get_field_val(ral.auto_block_out_ctl.key0_out_value, rdata);
      override_key1_out_value = get_field_val(ral.auto_block_out_ctl.key1_out_value, rdata);
      override_key2_out_value = get_field_val(ral.auto_block_out_ctl.key2_out_value, rdata);

      cfg.clk_aon_rst_vif.wait_clks(1);
      if(enable_key0_out_sel == 1) begin
       `DV_CHECK_EQ(override_key0_out_value, cfg.vif.key0_out);
      end
      if(enable_key1_out_sel == 1) begin
       `DV_CHECK_EQ(override_key1_out_value, cfg.vif.key1_out);
      end
      if(enable_key2_out_sel == 1) begin
       `DV_CHECK_EQ(override_key2_out_value, cfg.vif.key2_out);
      end

      // Disable the auto-block feature
      ral.auto_block_debounce_ctl.auto_block_enable.set(0);
      csr_update(ral.auto_block_debounce_ctl);

      cfg.clk_aon_rst_vif.wait_clks(10);
    end
   cfg.clk_aon_rst_vif.wait_clks(20);
   endtask : body

endclass : sysrst_ctrl_auto_blk_key_output_vseq

