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
   rand bit en_ulp;
   // TODO: z3_wakeup check logic could move to scb.
   uint16_t get_ac_timer, get_pwrb_timer, get_lid_timer;
   bit enable_ulp, exp_z3_wakeup;

   constraint set_pwrb_timer_c {
    set_pwrb_timer dist {
      [10:100] :/ 95,
      [101:$]  :/ 5
    };
   }

   constraint set_lid_timer_c {
    set_lid_timer dist {
      [10:100] :/ 95,
      [101:$]  :/ 5
    };
   }

   constraint set_ac_timer_c {
    set_ac_timer dist {
      [10:100] :/ 95,
      [101:$]  :/ 5
    };
   }

   constraint pwrb_cycles_c { pwrb_cycles dist {
       [1 : set_pwrb_timer]                      :/20,
       (set_pwrb_timer + 1)                      :/20,
       [set_pwrb_timer + 2 : set_pwrb_timer * 2] :/60
     };
   }
   constraint lid_cycles_c { lid_cycles dist {
       [1 : set_lid_timer]                     :/20,
       (set_lid_timer + 1)                     :/20,
       [set_lid_timer + 2 : set_lid_timer * 2] :/60
     };
   }
   constraint ac_cycles_c { ac_cycles dist {
       [1 : set_ac_timer]                    :/20,
       (set_ac_timer + 1)                    :/20,
       [set_ac_timer + 2 : set_ac_timer * 2] :/60
     };
   }

   constraint num_trans_c {num_trans inside {[1 : 3]};}

   task drive_ac();
    cfg.vif.ac_present = 1;
    for (int i = 0; i < ac_cycles; i++) begin
      if (exp_z3_wakeup == 0 && enable_ulp && i > get_ac_timer) begin
        `uvm_info(`gfn, "z3_wakeup assertion expected for a HIGH level on ac_present_i", UVM_LOW)
        exp_z3_wakeup = 1;
      end
      cfg.clk_aon_rst_vif.wait_clks(1);
    end
    cfg.vif.ac_present = 0;
   endtask

   task drive_pwrb();
    cfg.vif.pwrb_in = 1;
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(1,20));
    cfg.vif.pwrb_in = 0;
    for (int i = 0; i < pwrb_cycles; i++) begin
      if (exp_z3_wakeup == 0 && enable_ulp && i > get_pwrb_timer) begin
        exp_z3_wakeup = 1;
        `uvm_info(`gfn, "z3_wakeup assertion expected for a H2L transition on pwrb_in_i", UVM_LOW)
      end
      cfg.clk_aon_rst_vif.wait_clks(1);
    end
    cfg.vif.pwrb_in = 1;
   endtask

   task drive_lid();
    cfg.vif.lid_open = 0;
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(1,20));
    cfg.vif.lid_open = 1;
    for (int i = 0; i < lid_cycles; i++) begin
      if (exp_z3_wakeup == 0 && enable_ulp && i > get_lid_timer) begin
        exp_z3_wakeup = 1;
        `uvm_info(`gfn, "z3_wakeup assertion expected for a L2H transition on lid_open_i", UVM_LOW)
      end
      cfg.clk_aon_rst_vif.wait_clks(1);
    end
    cfg.vif.lid_open = 0;
   endtask

   task body();

     uvm_reg_data_t rdata, wkup_sts_rdata;

     `uvm_info(`gfn, "Starting the body from ultra_low_pwr_vseq", UVM_LOW)

     fork
       begin: z3_wakeup_check
         forever begin
           @(posedge cfg.vif.z3_wakeup);
           cfg.clk_aon_rst_vif.wait_n_clks(1);
           `DV_CHECK(exp_z3_wakeup, 1)
         end
       end: z3_wakeup_check
     join_none;

     repeat (num_trans) begin
       `DV_CHECK_MEMBER_RANDOMIZE_FATAL(en_ulp)

       // Enable ultra low power feature
       ral.ulp_ctl.ulp_enable.set(en_ulp);
       csr_update(ral.ulp_ctl);

       // Set the debounce timer for pwrb, ac and lid_open
       csr_wr(ral.ulp_ac_debounce_ctl, set_ac_timer);
       csr_wr(ral.ulp_lid_debounce_ctl, set_lid_timer);
       csr_wr(ral.ulp_pwrb_debounce_ctl, set_pwrb_timer);

       csr_rd(ral.ulp_ac_debounce_ctl, get_ac_timer);
       csr_rd(ral.ulp_pwrb_debounce_ctl, get_pwrb_timer);
       csr_rd(ral.ulp_lid_debounce_ctl, get_lid_timer);
       csr_rd(ral.ulp_ctl, rdata);
       enable_ulp = get_field_val(ral.ulp_ctl.ulp_enable, rdata);

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

         // Wait until all debounce timer expires, so the state machines will be reset to Idle.
         begin
           int wait_cycles[$];
           wait_cycles.push_back(cycles_to_finish_debounce(pwrb_cycles, set_pwrb_timer));
           wait_cycles.push_back(cycles_to_finish_debounce(lid_cycles, set_lid_timer));
           wait_cycles.push_back(cycles_to_finish_debounce(ac_cycles, set_ac_timer));
           cfg.clk_aon_rst_vif.wait_clks($urandom_range(2, 10) + max(wait_cycles));
         end
       end

       // Enable the bus clock to read the status register
       cfg.clk_rst_vif.start_clk();

       `uvm_info(`gfn, {$sformatf("enable_ulp=%0b, pwrb_cycles=%0d, pwrb_timer=%0d",
                                  enable_ulp, pwrb_cycles, get_pwrb_timer),
                        $sformatf("ac_cycles=%0d, get_ac_timer=%0d", ac_cycles, get_ac_timer),
                        $sformatf("lid_cycles=%0d, lid_timer=%0d", lid_cycles, get_lid_timer)},
                 UVM_MEDIUM)
       // (cycles == timer) => sysrst_ctrl_detect.state : DebounceSt -> IdleSt
       // (cycles == timer + 1) => sysrst_ctrl_detect.state : DetectSt -> IdleSt
       // Therefore we only need to check when cycles > timer + 1
       if (enable_ulp == 1 &&
           (pwrb_cycles > (get_pwrb_timer + 1) ||
            ac_cycles > (get_ac_timer + 1) ||
            lid_cycles > (get_lid_timer + 1))) begin
         cfg.clk_aon_rst_vif.wait_clks(1);
         `DV_CHECK_EQ(cfg.vif.z3_wakeup, 1);
         csr_rd(ral.wkup_status, wkup_sts_rdata);
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

         // Clear the wkup_status register
         csr_wr(ral.wkup_status, 'h1);
         cfg.clk_aon_rst_vif.wait_clks(20);

         // Check if the register is cleared
         csr_rd_check(ral.wkup_status, .compare_value(0));

         // Check z3_wakeup reset back to 0
         `DV_CHECK_EQ(cfg.vif.z3_wakeup, 0);
         exp_z3_wakeup = 0;
       end else begin
         `DV_CHECK_EQ(cfg.vif.z3_wakeup, 0);
         `DV_CHECK_EQ(exp_z3_wakeup, 0);
         csr_rd(ral.wkup_status,wkup_sts_rdata);
         csr_rd_check(ral.wkup_status, .compare_value(0));
         csr_rd_check(ral.ulp_status, .compare_value(0));
       end

       // Sample the wakeup event covergroup before clearing the status register
       if (cfg.en_cov) begin
         cov.wakeup_event.sysrst_ctrl_wkup_event_cg.sample(
             get_field_val(ral.wkup_status.wakeup_sts, wkup_sts_rdata),
             cfg.vif.pwrb_in,
             cfg.vif.lid_open,
             cfg.vif.ac_present,
             cfg.intr_vif.pins
         );
       end
       cfg.clk_aon_rst_vif.wait_clks($urandom_range(0, 10));
     end
     disable z3_wakeup_check;
     `uvm_info(`gfn, "Disble Z3 wakeup check", UVM_LOW)
   endtask : body

   // A helper function to determine if the set time is long enough to cover the debounce state.
   // If the set time is longer than the debounce time, return 0.
   // If the set time if shorter than the debounce time, return the cycles required to finish
   // the debounce state.
   virtual function uint cycles_to_finish_debounce(int set_cycles, int debounce_timer);
     return (set_cycles >= debounce_timer) ? 0 : (debounce_timer - set_cycles);
   endfunction

endclass : sysrst_ctrl_ultra_low_pwr_vseq
