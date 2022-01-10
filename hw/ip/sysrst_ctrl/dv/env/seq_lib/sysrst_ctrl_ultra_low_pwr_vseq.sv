// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will verify the ultra low power feature.
class sysrst_ctrl_ultra_low_pwr_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_ultra_low_pwr_vseq)

  `uvm_object_new

   rand uint16_t set_pwrb_timer, set_lid_timer, set_ac_timer, min_timer;

   task body();

    uvm_reg_data_t rdata;

    `uvm_info(`gfn, "Starting the body from ultra_low_pwr_vseq", UVM_LOW)

    repeat ($urandom_range(1,5)) begin
     // Enable ultra low power feature
     ral.ulp_ctl.ulp_enable.set(1);
     csr_update(ral.ulp_ctl);

     // Set the debounce timer for pwrb, ac and lid_open
     csr_wr(ral.ulp_ac_debounce_ctl, set_ac_timer);
     csr_wr(ral.ulp_lid_debounce_ctl, set_lid_timer);
     csr_wr(ral.ulp_pwrb_debounce_ctl, set_pwrb_timer);

     // Disable the bus clock
     cfg.clk_rst_vif.stop_clk();

     // It takes 2-3 clock cycles to sync the register values
     cfg.clk_aon_rst_vif.wait_clks(2);

     repeat ($urandom_range(2,10)) begin
      cfg.clk_aon_rst_vif.wait_clks(1);
      cfg.vif.randomize_input();
     end

     // It takes 3 clk cycles to det the trigger and start the timer
     cfg.clk_aon_rst_vif.wait_clks(3);

     // Wait till the first timer is finished
     min_timer = min2(set_lid_timer, set_ac_timer);
     min_timer = min2(min_timer, set_pwrb_timer);

     cfg.clk_aon_rst_vif.wait_clks(min_timer);

     // Wait for sometime before starting the clock
     cfg.clk_aon_rst_vif.wait_clks(3);

     // Enable the bus clock to read the status register
     cfg.clk_rst_vif.start_clk();

     cfg.clk_rst_vif.wait_clks(3);

     if (cfg.vif.z3_wakeup == 1) begin

      // Check if the ulp wakeup event is detected
      csr_rd_check(ral.ulp_status, .compare_value(1));

      // Clear the ulp_status register
      csr_wr(ral.ulp_status, 'h1);

      cfg.clk_aon_rst_vif.wait_clks(20);
      // Check if the register is cleared
      csr_rd_check(ral.ulp_status, .compare_value(0));

     end else begin
      csr_rd_check(ral.ulp_status, .compare_value(0));
     end

     // Disable the ultra low power feature
     ral.ulp_ctl.ulp_enable.set(0);
     csr_update(ral.ulp_ctl);
     #100us;
    end
     #100us;
   endtask : body

endclass : sysrst_ctrl_ultra_low_pwr_vseq
