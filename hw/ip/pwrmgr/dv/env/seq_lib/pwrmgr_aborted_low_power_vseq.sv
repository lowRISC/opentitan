// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The aborted low power test causes low power transitions to abort for CPU interrupts and nvms not
// idle. It randomly enables wakeups, info capture, and interrupts, and sends wakeups at random
// times, but causes a test failure if they are not aborted.
class pwrmgr_aborted_low_power_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_aborted_low_power_vseq)

  `uvm_object_new

  // If set causes an abort because the CPU gets an interrupt, which shows up as
  // pwr_cpu.core_sleeping being low when the fast FSM is in FastPwrStateFallThrough.
  rand bit cpu_interrupt;
  rand bit flash_idle;
  rand bit lc_idle;
  rand bit otp_idle;

  constraint idle_c {
    solve cpu_interrupt before flash_idle, lc_idle, otp_idle;
    if (!cpu_interrupt) {flash_idle & lc_idle & otp_idle == 1'b0;}
  }

  constraint wakeups_c {wakeups != 0;}

  constraint wakeup_en_c {
    solve wakeups before wakeups_en;
    |(wakeups_en & wakeups) == 1'b1;
  }

  // Make sure wakeup capture is enabled to check the abort happened.
  constraint enable_wakeup_capture_c {disable_wakeup_capture == 1'b0;}

  task body();
    logic [TL_DW-1:0] value;
    wakeups_t enabled_wakeups;

    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(0));
    set_nvms_idle();
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));
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

      // Defeat the low power entry.
      if (cpu_interrupt) begin
        // The transition back to cpu active must be soon enough.
        `uvm_info(`gfn, "Expecting a fall_through (0x40)", UVM_MEDIUM)
        set_nvms_idle();
        cfg.clk_rst_vif.wait_clks(2);
        cfg.pwrmgr_vif.update_cpu_sleeping(1'b0);
      end else begin
        `uvm_info(`gfn, "Expecting an abort (0x80)", UVM_MEDIUM)
        set_nvms_idle(flash_idle, lc_idle, otp_idle);
      end
      // Wait enough time for the clocks to be turned off and then wait for them to go back on,
      // indicating the fast fsm is active again.
      cfg.clk_rst_vif.wait_clks(2);
      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      // Check there was no reset.
      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0),
                   .err_msg("failed reset_status check"));

      // No wakeups, but check abort and fall_through.
      if (cpu_interrupt) begin
        check_wake_info(.reasons('0), .fall_through(1'b1), .abort(1'b0));
      end else begin
        check_wake_info(.reasons('0), .fall_through(1'b0), .abort(1'b1));
      end
      clear_wake_info();

      // And check interrupt is set.
      check_and_clear_interrupt(.expected(1'b1));

      // Get ready for another round.
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b0);
      set_nvms_idle();
    end
    `uvm_info(`gfn, "Test done", UVM_MEDIUM)
  endtask

endclass : pwrmgr_aborted_low_power_vseq
