// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The wakeup test randomly enables wakeups, info capture, and interrupts,
// and sends wakeups at random times.
class pwrmgr_wakeup_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_wakeup_vseq)

  `uvm_object_new

  constraint wakeups_c {wakeups != 0;}

  rand bit prior_wakeup;
  rand wakeups_t prior_wakeups;
  constraint prior_wakeups_c {
    solve wakeups, prior_wakeup before prior_wakeups;
    if (prior_wakeup) {
      prior_wakeups != 0;
      prior_wakeups != wakeups;
    }
  }

  constraint wakeup_en_c {
    solve wakeups before wakeups_en;
    |(wakeups_en & wakeups) == 1'b1;
  }

  task body();
    logic [TL_DW-1:0] value;
    wakeups_t enabled_wakeups;

    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(0));
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Enable wakeups.
      enabled_wakeups = wakeups_en & wakeups;
      `DV_CHECK(enabled_wakeups, $sformatf(
                "Some wakeup must be enabled: wkups=%b, wkup_en=%b", wakeups, wakeups_en))
      `uvm_info(`gfn, $sformatf("Enabled wakeups=0x%x", enabled_wakeups), UVM_MEDIUM)
      csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeups_en));
      `uvm_info(`gfn, $sformatf("%0sabling wakeup capture", disable_wakeup_capture ? "Dis" : "En"),
                UVM_MEDIUM)
      csr_wr(.ptr(ral.wake_info_capture_dis), .value(disable_wakeup_capture));

      update_control_enables(1'b1);

      wait_for_csr_to_propagate_to_slow_domain();
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);

      // Initiate low power transition.
      fast_to_low_power();
      if (ral.control.main_pd_n.get_mirrored_value() == 1'b0) begin
        wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);
      end

      // Now bring it back.
      cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
      cfg.pwrmgr_vif.update_wakeups(wakeups);
      // Check wake_status prior to wakeup, or the unit requesting wakeup will have been reset.
      // This read will not work in the chip, since the processor will be asleep.
      cfg.slow_clk_rst_vif.wait_clks(4);
      csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(enabled_wakeups),
                   .err_msg("failed wake_status check"));
      `uvm_info(`gfn, $sformatf("Got wake_status=0x%x", enabled_wakeups), UVM_MEDIUM)
      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from wakeup", UVM_MEDIUM)

      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0),
                   .err_msg("failed reset_status check"));

      check_wake_info(enabled_wakeups, .fall_through(1'b0), .abort(1'b0));

      // To clear wake_info capture must be disabled.
      csr_wr(.ptr(ral.wake_info_capture_dis), .value(1'b1));
      csr_wr(.ptr(ral.wake_info), .value('1));

      // This is the expected side-effect of the low power entry reset, since the source of the
      // non-aon wakeup sources will deassert it as a consequence of their reset.
      // Some aon wakeups may remain active until software clears them. If they didn't, such wakeups
      // will remain active, preventing the device from going to sleep.
      cfg.pwrmgr_vif.update_wakeups('0);

      // Wait for interrupt to be generated whether or not it is enabled.
      cfg.slow_clk_rst_vif.wait_clks(10);
      csr_rd_check(.ptr(ral.wake_status[0]), .compare_value('0));
    end
  endtask

endclass : pwrmgr_wakeup_vseq
