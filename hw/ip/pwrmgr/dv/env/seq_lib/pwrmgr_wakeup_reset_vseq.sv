// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The wakeup_reset test randomly enables wakeups and resets, info capture, and interrupts,
// and sends wakeups and resets in close temporal proximity at random times.
class pwrmgr_wakeup_reset_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_wakeup_reset_vseq)

  `uvm_object_new

  constraint wakeups_c {wakeups != 0;}

  constraint wakeup_en_c {
    solve wakeups before wakeups_en;
    |(wakeups_en & wakeups) == 1'b1;
  }
  constraint disable_wakeup_capture_c {disable_wakeup_capture == 1'b0;}

  task body();
    logic [TL_DW-1:0] value;
    resets_t enabled_resets;
    wakeups_t enabled_wakeups;

    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0));
    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(0));
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Enable resets.
      enabled_resets = resets_en & resets;
      `uvm_info(`gfn, $sformatf(
                "Enabled resets=0x%x, power_reset=%b, escalation=%b, sw_reset=%b",
                enabled_resets,
                power_glitch_reset,
                escalation_reset,
                sw_rst_from_rstmgr
                ), UVM_MEDIUM)
      csr_wr(.ptr(ral.reset_en[0]), .value(resets_en));

      // Enable wakeups.
      enabled_wakeups = wakeups_en & wakeups;
      `DV_CHECK(enabled_wakeups, $sformatf(
                "Some wakeup must be enabled: wkups=%b, wkup_en=%b", wakeups, wakeups_en))
      `uvm_info(`gfn, $sformatf("Enabled wakeups=0x%x", enabled_wakeups), UVM_MEDIUM)
      csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeups_en));

      clear_wake_info();

      `uvm_info(`gfn, $sformatf("%0sabling wakeup capture", disable_wakeup_capture ? "Dis" : "En"),
                UVM_MEDIUM)
      csr_wr(.ptr(ral.wake_info_capture_dis), .value(disable_wakeup_capture));

      update_control_enables(1'b1);

      wait_for_csr_to_propagate_to_slow_domain();

      // Initiate low power transition.
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
      set_nvms_idle();

      // Wait for the slow state machine to be in low power.
      wait (cfg.pwrmgr_vif.slow_state == pwrmgr_pkg::SlowPwrStateLowPower);

      // This will send the wakeup and reset so they almost coincide.
      fork
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_reset);
          cfg.pwrmgr_vif.update_resets(resets);
          cfg.pwrmgr_vif.update_sw_rst_req(sw_rst_from_rstmgr);
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
          cfg.pwrmgr_vif.update_wakeups(wakeups);
        end
      join

      // Check wake_status prior to wakeup, or the unit requesting wakeup will have been reset.
      // This read will not work in the chip, since the processor will be asleep.
      cfg.slow_clk_rst_vif.wait_clks(4);
      csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(enabled_wakeups),
                   .err_msg("failed wake_status check"));
      `uvm_info(`gfn, $sformatf("Got wake_status=0x%x", enabled_wakeups), UVM_MEDIUM)
      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(enabled_resets),
                   .err_msg("failed reset_status check"));
      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      wait_for_fast_fsm_active();

      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0),
                   .err_msg("failed reset_status check"));

      check_wake_info(.reasons(enabled_wakeups), .prior_reasons(1'b0), .fall_through(1'b0),
                      .prior_fall_through(1'b0), .abort(1'b0),
                      .prior_abort(1'b0));

      // This is the expected side-effect of the low power entry reset, since the source of the
      // non-aon wakeup sources will deassert it as a consequence of their reset.
      // Some aon wakeups may remain active until software clears them. If they didn't, such wakeups
      // will remain active, preventing the device from going to sleep.
      cfg.pwrmgr_vif.update_wakeups('0);
      cfg.slow_clk_rst_vif.wait_clks(10);
      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value('0));
      csr_rd_check(.ptr(ral.wake_status[0]), .compare_value('0));

      // Wait for interrupt to be generated whether or not it is enabled.
      cfg.slow_clk_rst_vif.wait_clks(10);
    end
  endtask

endclass : pwrmgr_wakeup_reset_vseq
