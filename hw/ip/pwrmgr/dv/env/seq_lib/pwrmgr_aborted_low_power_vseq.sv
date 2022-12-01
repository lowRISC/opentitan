// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The aborted low power test causes low power transitions to abort for CPU interrupts and nvms not
// idle. It randomly enables wakeups, info capture, and interrupts, and sends wakeups at random
// times, and causes a test failure if they are not aborted.
class pwrmgr_aborted_low_power_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_aborted_low_power_vseq)

  `uvm_object_new

  // If set causes an abort because the CPU gets an interrupt, which shows up as
  // pwr_cpu.core_sleeping being low when the fast FSM is in FastPwrStateFallThrough.
  rand bit cpu_interrupt;

  constraint cpu_interrupt_c {
    cpu_interrupt dist {
      1 := 2,
      0 := 6
    };
  }

  rand bit flash_idle;
  rand bit lc_idle;
  rand bit otp_idle;

  constraint idle_c {
    solve cpu_interrupt before flash_idle, lc_idle, otp_idle;
    if (!cpu_interrupt) {(flash_idle && lc_idle && otp_idle) == 1'b0;}
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
    wait_for_fast_fsm_active();

    check_wake_status('0);
    set_nvms_idle();
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));
      // Enable wakeups.
      enabled_wakeups = wakeups_en & wakeups;
      `DV_CHECK(enabled_wakeups, $sformatf(
                "Some wakeup must be enabled: wkups=%b, wkup_en=%b", wakeups, wakeups_en))
      `uvm_info(`gfn, $sformatf(
                "Enabled wakeups=0x%x (wkups=%x  wkup_en=%x)", enabled_wakeups, wakeups, wakeups_en
                ), UVM_MEDIUM)
      csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeups_en));
      `uvm_info(`gfn, $sformatf("%0sabling wakeup capture", disable_wakeup_capture ? "Dis" : "En"),
                UVM_MEDIUM)
      csr_wr(.ptr(ral.wake_info_capture_dis), .value(disable_wakeup_capture));
      low_power_hint = 1'b1;

      // Put CPU to sleep even before the control registers are fully written to avoid
      // unexpected failures to abort due to delicate timing.
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);

      fork
        begin
          update_control_csr();
          `uvm_info(`gfn, $sformatf("After update_control_csr exp_intr=%b", exp_intr), UVM_MEDIUM)
        end
        begin
          // Prepare for an abort ahead of time.
          `DV_WAIT(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive)
          // Wait one more cycle for update_control_csr called above to predict the interrupt
          // based on the value of cpu_sleeping right after the transition out of active state.
          // There is enough time for this since it takes time to disable the clocks.
          cfg.clk_rst_vif.wait_clks(1);
          if (cpu_interrupt) begin
            `uvm_info(`gfn, "Expecting a fall through (0x40)", UVM_MEDIUM)
            cfg.pwrmgr_vif.update_cpu_sleeping(1'b0);
          end else begin
            `uvm_info(`gfn, $sformatf(
                      "Expecting an abort (0x80): fi=%b, li=%b, oi=%b",
                      flash_idle,
                      lc_idle,
                      otp_idle
                      ), UVM_MEDIUM)
            set_nvms_idle(flash_idle, lc_idle, otp_idle);
          end
        end
      join
      wait_for_fast_fsm_active();

      `uvm_info(`gfn, "Back from sleep attempt", UVM_MEDIUM)
      @cfg.clk_rst_vif.cb;

      // No wakeups, but check abort and fall_through.
      fork
        begin
          fast_check_reset_status(0);
        end
        begin
          fast_check_wake_info(.reasons('0), .fall_through(cpu_interrupt), .abort(~cpu_interrupt));
        end
      join

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
