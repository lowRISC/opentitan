// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will detect the edge transition on input keys
// and raise an interrupt
class sysrst_ctrl_edge_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_edge_detect_vseq)

  `uvm_object_new

   rand uvm_reg_data_t set_input, set_timer;

   constraint timer_c {set_timer <= 'hffff;}

   task body();

       uvm_reg_data_t rdata;
       bit en_pwrb_in_h2l, en_key0_in_h2l, en_key1_in_h2l, en_key2_in_h2l, 
           en_ac_present_h2l, en_ec_rst_l_h2l;
       bit en_pwrb_in_l2h, en_key0_in_l2h, en_key1_in_l2h, en_key2_in_l2h,
           en_ac_present_l2h, en_ec_rst_l_l2h;
       bit set_pwrb_h2l, set_key0_in_h2l, set_key1_in_h2l, set_key2_in_h2l,
           set_ac_present_h2l, set_ec_rst_l_h2l;
       bit set_pwrb_l2h, set_key0_in_l2h, set_key1_in_l2h, set_key2_in_l2h,
           set_ac_present_l2h, set_ec_rst_l_l2h;

      `uvm_info(`gfn, "Starting the body from edge_detect_vseq", UVM_LOW)

       // Select the inputs and their transition
       csr_wr(ral.key_intr_ctl, set_input);

       // Set the key interrupt debounce timer value
       csr_wr(ral.key_intr_debounce_ctl, set_timer);

       // It takes 2-3 clock cycles to sync register values
       cfg.clk_aon_rst_vif.wait_clks(2);

      // Randomize and trigger the input pins
      repeat ($urandom_range(1,5)) begin
        //Press the input keys
        cfg.clk_aon_rst_vif.wait_clks(1);
        cfg.vif.randomize_input();
      end

       // Wait for the timer to reach the value configured to debounce_timer
       cfg.clk_aon_rst_vif.wait_clks(set_timer);

       // Wait for sometime before starting the clock
       cfg.clk_aon_rst_vif.wait_clks(3);

       // Read the key_intr_ctl register and find the inputs that are enabled
       csr_rd(ral.key_intr_ctl, rdata);

       en_pwrb_in_h2l = get_field_val(ral.key_intr_ctl.pwrb_in_h2l, rdata);
       en_key0_in_h2l = get_field_val(ral.key_intr_ctl.key0_in_h2l, rdata);
       en_key1_in_h2l = get_field_val(ral.key_intr_ctl.key1_in_h2l, rdata);
       en_key2_in_h2l = get_field_val(ral.key_intr_ctl.key2_in_h2l, rdata);
       en_ac_present_h2l = get_field_val(ral.key_intr_ctl.ac_present_h2l, rdata);
       en_ec_rst_l_h2l = get_field_val(ral.key_intr_ctl.ec_rst_l_h2l, rdata);

       en_pwrb_in_l2h = get_field_val(ral.key_intr_ctl.pwrb_in_l2h, rdata);
       en_key0_in_l2h = get_field_val(ral.key_intr_ctl.key0_in_l2h, rdata);
       en_key1_in_l2h = get_field_val(ral.key_intr_ctl.key1_in_l2h, rdata);
       en_key2_in_l2h = get_field_val(ral.key_intr_ctl.key2_in_l2h, rdata);
       en_ac_present_l2h = get_field_val(ral.key_intr_ctl.ac_present_l2h, rdata);
       en_ec_rst_l_l2h = get_field_val(ral.key_intr_ctl.ec_rst_l_l2h, rdata);

       // Read the key_intr_status register
       csr_rd(ral.key_intr_status, rdata);

       set_pwrb_h2l = get_field_val(ral.key_intr_status.pwrb_h2l, rdata);
       set_key0_in_h2l = get_field_val(ral.key_intr_status.key0_in_h2l, rdata);
       set_key1_in_h2l = get_field_val(ral.key_intr_status.key1_in_h2l, rdata);
       set_key2_in_h2l = get_field_val(ral.key_intr_status.key2_in_h2l, rdata);
       set_ac_present_h2l = get_field_val(ral.key_intr_status.ac_present_h2l, rdata);
       set_ec_rst_l_h2l = get_field_val(ral.key_intr_status.ec_rst_l_h2l, rdata);

       set_pwrb_l2h = get_field_val(ral.key_intr_status.pwrb_l2h, rdata);
       set_key0_in_l2h = get_field_val(ral.key_intr_status.key0_in_l2h, rdata);
       set_key1_in_l2h = get_field_val(ral.key_intr_status.key1_in_l2h, rdata);
       set_key2_in_l2h = get_field_val(ral.key_intr_status.key2_in_l2h, rdata);
       set_ac_present_l2h = get_field_val(ral.key_intr_status.ac_present_l2h, rdata);
       set_ec_rst_l_l2h = get_field_val(ral.key_intr_status.ec_rst_l_l2h, rdata);

       cfg.clk_aon_rst_vif.wait_clks(1);
       `DV_CHECK_EQ(en_pwrb_in_h2l, set_pwrb_h2l)
       `DV_CHECK_EQ(en_key0_in_h2l, set_key0_in_h2l)
       `DV_CHECK_EQ(en_key1_in_h2l, set_key1_in_h2l)
       `DV_CHECK_EQ(en_key2_in_h2l, set_key2_in_h2l)
       `DV_CHECK_EQ(en_ac_present_h2l, set_ac_present_h2l)
       `DV_CHECK_EQ(en_ec_rst_l_h2l, set_ec_rst_l_h2l)

       `DV_CHECK_EQ(en_pwrb_in_l2h, set_pwrb_l2h)
       `DV_CHECK_EQ(en_key0_in_l2h, set_key0_in_l2h)
       `DV_CHECK_EQ(en_key1_in_l2h, set_key1_in_l2h)
       `DV_CHECK_EQ(en_key2_in_l2h, set_key2_in_l2h)
       `DV_CHECK_EQ(en_ac_present_l2h, set_ac_present_l2h)
       `DV_CHECK_EQ(en_ec_rst_l_l2h, set_ec_rst_l_l2h)

       // Write to clear the register
       csr_wr(ral.key_intr_status, rdata);

       cfg.clk_aon_rst_vif.wait_clks(20);
       // Check if the register is cleared
       csr_rd_check(ral.key_intr_status, .compare_value(0));

       cfg.clk_aon_rst_vif.wait_clks(20);
   endtask : body

endclass : sysrst_ctrl_edge_detect_vseq

