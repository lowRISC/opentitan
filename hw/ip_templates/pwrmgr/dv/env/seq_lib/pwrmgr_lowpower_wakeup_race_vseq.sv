// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The lowpower_wakeup race test randomly enables wakeups, info capture, and interrupts,
// and sends wakeups in the temporal vecinity of low power entry. It also sends wakeups
// after wakeup processing starts.
class pwrmgr_lowpower_wakeup_race_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_lowpower_wakeup_race_vseq)

  `uvm_object_new

  constraint wakeups_c {wakeups != 0;}

  rand bit keep_prior_wake_info;

  constraint wakeup_en_c {
    solve wakeups before wakeups_en;
    |(wakeups_en & wakeups) == 1'b1;
  }

  rand int cycles_before_early_wakeup;
  rand int cycles_before_transition;
  constraint cycles_racing_c {
    cycles_before_early_wakeup inside {[2 : 8]};
    cycles_before_transition inside {[2 : 8]};
  }

  task body();
    logic [TL_DW-1:0] value;
    wakeups_t prior_reasons = '0;
    bit prior_fall_through = '0;
    bit prior_abort = '0;
    wait_for_fast_fsm_active();

    check_wake_status('0);
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));

      csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeups_en));
      `uvm_info(`gfn, $sformatf("Enabled wakeups=0x%x", wakeups_en & wakeups), UVM_MEDIUM)

      if (keep_prior_wake_info) begin
        csr_rd(.ptr(ral.wake_info.reasons), .value(prior_reasons));
        csr_rd(.ptr(ral.wake_info.fall_through), .value(prior_fall_through));
        csr_rd(.ptr(ral.wake_info.abort), .value(prior_abort));
      end else begin
        clear_wake_info();
        prior_reasons = '0;
        prior_fall_through = '0;
        prior_abort = '0;
      end
      `uvm_info(`gfn, $sformatf(
                "Prior wake_info: reasons=0x%x, fall_through=%b, abort=%b",
                prior_reasons,
                prior_fall_through,
                prior_abort
                ), UVM_MEDIUM)

      `uvm_info(`gfn, $sformatf("%0sabling wakeup capture", disable_wakeup_capture ? "Dis" : "En"),
                UVM_MEDIUM)
      csr_wr(.ptr(ral.wake_info_capture_dis), .value(disable_wakeup_capture));

      low_power_hint = 1'b1;
      update_control_csr();

      wait_for_csr_to_propagate_to_slow_domain();
      set_nvms_idle();

      // This will send the wakeup and trigger low power entry so they almost coincide.
      fork
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_transition);
          // Initiate low power transition.
          cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_early_wakeup);
          // Send the wakeups.
          cfg.pwrmgr_vif.update_wakeups(wakeups);
        end
      join

      if (ral.control.main_pd_n.get_mirrored_value() == 1'b0) begin
        wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);
      end

      // Now bring it back.
      cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);

      // Check wake_status prior to wakeup, or the unit requesting wakeup will have been reset.
      // This read will not work in the chip, since the processor will be asleep.
      cfg.slow_clk_rst_vif.wait_clks(5);
      check_wake_status(wakeups & wakeups_en);
      `uvm_info(`gfn, $sformatf("Got wake_status=0x%x", wakeups & wakeups_en), UVM_MEDIUM)
      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      // Send more wakeups to make sure they are reported in CSRs. With this all enabled
      // wakeups should be registered.
      cfg.pwrmgr_vif.update_wakeups('1);

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from wakeup", UVM_MEDIUM)

      // make this check parallel.
      // to avoid csr rd blocking later status read request and
      // miss status update window.
      @cfg.clk_rst_vif.cb;
      fork
        begin
          fast_check_reset_status(0);
        end
        begin
          fast_check_wake_info(.reasons(wakeups_en), .prior_reasons(prior_reasons),
                               .fall_through(1'b0), .abort(1'b0),
                               .prior_fall_through(prior_fall_through), .prior_abort(prior_abort));
        end
      join
      // This is the expected side-effect of the low power entry reset, since the source of the
      // non-aon wakeup sources will deassert it as a consequence of their reset.
      // Some aon wakeups may remain active until software clears them. If they didn't, such wakeups
      // will remain active, preventing the device from going to sleep.
      cfg.pwrmgr_vif.update_wakeups('0);
      cfg.slow_clk_rst_vif.wait_clks(10);
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b0);

      // wait for clock is on
      cfg.clk_rst_vif.wait_clks(10);

      check_wake_status('0);

      // Wait for interrupt to be generated whether or not it is enabled.
      cfg.slow_clk_rst_vif.wait_clks(10);
      check_and_clear_interrupt(.expected(1'b1));
    end
    clear_wake_info();
  endtask

endclass : pwrmgr_lowpower_wakeup_race_vseq
