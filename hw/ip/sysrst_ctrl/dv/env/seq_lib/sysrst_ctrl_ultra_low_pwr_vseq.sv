// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will verify the ultra low power feature. It detects the specific
// signal transition on pwrb_in, ac_present and lid_open pins, starts the timer
// configured in registers. Once the timing condition is met, ulp_status and wkup_status
// registers gets updated with the triggered event. Software will read and clear the register.
class sysrst_ctrl_ultra_low_pwr_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_ultra_low_pwr_vseq)

  `uvm_object_new

   rand uint16_t set_pwrb_timer, set_lid_timer, set_ac_timer;
   rand int pwrb_cycles, ac_cycles, lid_cycles;

   constraint set_pwrb_timer_c {
    set_pwrb_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
   }

   constraint set_lid_timer_c {
    set_lid_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
   }

   constraint set_ac_timer_c {
    set_ac_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
   }

   constraint pwrb_cycles_c { pwrb_cycles dist {
     [set_pwrb_timer - 10 : set_pwrb_timer] :/5,
     [set_pwrb_timer : set_pwrb_timer + 2] :/95 };}
   constraint lid_cycles_c { lid_cycles dist {
     [set_lid_timer - 10 : set_lid_timer] :/5,
     [set_lid_timer : set_lid_timer + 2] :/95 };}
   constraint ac_cycles_c { ac_cycles dist {
     [set_ac_timer - 10: set_ac_timer]  :/5,
     [set_ac_timer : set_ac_timer + 2] :/95 };}

   task drive_ac();
    cfg.vif.ac_present = 1;
    cfg.clk_aon_rst_vif.wait_clks(ac_cycles+1);
    cfg.vif.ac_present = 0;
   endtask

   task drive_pwrb();
    cfg.vif.pwrb_in = 1;
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(1,20));
    cfg.vif.pwrb_in = 0;
    cfg.clk_aon_rst_vif.wait_clks(pwrb_cycles+1);
    cfg.vif.pwrb_in = 1;
   endtask

   task drive_lid();
    cfg.vif.lid_open = 0;
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(1,20));
    cfg.vif.lid_open = 1;
    cfg.clk_aon_rst_vif.wait_clks(lid_cycles+1);
    cfg.vif.lid_open = 0;
   endtask

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

     repeat ($urandom_range(1,5)) begin
      fork
        begin
          cfg.clk_aon_rst_vif.wait_clks(1);
          drive_pwrb();
        end
        begin
          cfg.clk_aon_rst_vif.wait_clks(1);
          drive_ac();
        end
        begin
          cfg.clk_aon_rst_vif.wait_clks(1);
          drive_lid();
        end
      join
     end

     // Enable the bus clock to read the status register
     cfg.clk_rst_vif.start_clk();

     if (pwrb_cycles >= set_pwrb_timer || ac_cycles >= set_ac_timer ||
         lid_cycles >= set_lid_timer) begin
      cfg.clk_aon_rst_vif.wait_clks(1);
      `DV_CHECK_EQ(cfg.vif.z3_wakeup, 1);
      csr_rd_check(ral.wkup_status, .compare_value(1));
      // Check if the ulp wakeup event is detected
      csr_rd_check(ral.ulp_status, .compare_value(1));

      // Clear the ulp_status register
      csr_wr(ral.ulp_status, 'h1);

      cfg.clk_aon_rst_vif.wait_clks(20);
      // Check if the register is cleared
      csr_rd_check(ral.ulp_status, .compare_value(0));

      // Disable the ultra low power feature
      ral.ulp_ctl.ulp_enable.set(0);
      csr_update(ral.ulp_ctl);
    end else begin
      `DV_CHECK_EQ(cfg.vif.z3_wakeup, 0);
      csr_rd_check(ral.wkup_status, .compare_value(0));
      csr_rd_check(ral.ulp_status, .compare_value(0));
    end
     cfg.clk_aon_rst_vif.wait_clks(10);
    end
   endtask : body

endclass : sysrst_ctrl_ultra_low_pwr_vseq
