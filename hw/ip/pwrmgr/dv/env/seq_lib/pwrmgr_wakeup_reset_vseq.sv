// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The wakeup_reset test randomly enables wakeups and resets, info capture, and interrupts,
// and sends wakeups and resets in close temporal proximity at random times.
// Notice it makes no sense to send escalation reset requests while in low
// power, when the clocks are stopped, or while the system is already in reset
// since escalation should not be triggered with reset active.
class pwrmgr_wakeup_reset_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_wakeup_reset_vseq)

  `uvm_object_new

  constraint wakeups_c {wakeups != 0;}

  constraint wakeup_en_c {
    solve wakeups before wakeups_en;
    (wakeups_en & wakeups) != 0;
  }
  constraint disable_wakeup_capture_c {disable_wakeup_capture == 1'b0;}

  // Disabling escalation resets per comment above.
  constraint escalation_reset_c {escalation_reset == 0;}

  // Cause some delays for the rom_ctrl done and good inputs. Simple, enough to hold the
  // transition to active state.
  // ICEBOX(lowrisc/opentitan#18236) Consider adding checks to monitor fast state transitions are
  // compliant with "ROM Integrity Checks" at
  // https://opentitan.org/book/hw/ip/pwrmgr/doc/theory_of_operation.html#rom-integrity-checks
  virtual task twirl_rom_response();
    cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4False;
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
    @(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateAckPwrUp);
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
    @(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone);
    cfg.clk_rst_vif.wait_clks(10);
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
    cfg.clk_rst_vif.wait_clks(5);
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
    cfg.clk_rst_vif.wait_clks(5);
    cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
  endtask

  task body();
    logic [TL_DW-1:0] value;
    resets_t enabled_resets;
    wakeups_t enabled_wakeups;

    wait_for_fast_fsm_active();

    check_reset_status('0);
    check_wake_status('0);
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));

      // Enable resets.
      enabled_resets = resets_en & resets;
      `uvm_info(`gfn, $sformatf(
                "Enabled resets=0x%x, power_reset=%b, sw_reset=%b",
                enabled_resets,
                power_glitch_reset,
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

      low_power_hint = 1'b1;
      update_control_csr();
      wait_for_csr_to_propagate_to_slow_domain();

      // Initiate low power transition.
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
      set_nvms_idle();
      // Wait for the slow state machine to be in low power.
      wait(cfg.pwrmgr_vif.slow_state == pwrmgr_pkg::SlowPwrStateLowPower);
      // This will send the wakeup and reset so they almost coincide.
      // at low power state, do not use clk_rst_vif, cause it is off.
      fork
        begin
          cfg.slow_clk_rst_vif.wait_clks(cycles_before_reset);
          cfg.pwrmgr_vif.update_resets(resets);

          if (power_glitch_reset) begin
            send_power_glitch();
            enabled_resets = 0;
          end
          `uvm_info(`gfn, $sformatf("Sending reset=%b, power_glitch=%b", resets, power_glitch_reset
                    ), UVM_MEDIUM)
        end

        begin
          cfg.slow_clk_rst_vif.wait_clks(cycles_before_wakeup);
          cfg.pwrmgr_vif.update_wakeups(wakeups);
          `uvm_info(`gfn, $sformatf("Sending wakeup=%b", wakeups), UVM_MEDIUM)
        end
      join

      if (cfg.en_cov) begin
        cov.reset_wakeup_distance_cg.sample(cycles_before_reset - cycles_before_wakeup);
      end
      // twirl_rom_response has some waits, and so does the code to check wake_status,
      // so we fork them to avoid conflicts.

      fork
        begin
          // At lowpower state, wait for clock comes back before check any csr
          @cfg.clk_rst_vif.cb;
          // Check wake_status prior to wakeup, or the unit requesting wakeup will have been reset.
          // This read will not work in the chip, since the processor will be asleep.
          // Reset status cannot be reliably checked here since it is cleared when reset goes active.
          fast_check_wake_status(enabled_wakeups);
          `uvm_info(`gfn, $sformatf("Got wake_status=0x%x", enabled_wakeups), UVM_MEDIUM)
        end
        twirl_rom_response();
      join

      wait_for_fast_fsm_active();

      check_reset_status('0);

      check_wake_info(.reasons(enabled_wakeups), .prior_reasons(1'b0), .fall_through(1'b0),
                      .prior_fall_through(1'b0), .abort(1'b0), .prior_abort(1'b0));

      if (mubi_mode == PwrmgrMubiRomCtrl) begin
        add_rom_rsp_noise();
        cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
        cfg.clk_rst_vif.wait_clks(5);
        cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
      end

      // This is the expected side-effect of the low power entry reset, since the source of the
      // non-aon wakeup sources will deassert it as a consequence of their reset.
      // Some aon wakeups may remain active until software clears them. If they didn't, such wakeups
      // will remain active, preventing the device from going to sleep.
      cfg.pwrmgr_vif.update_wakeups('0);
      cfg.slow_clk_rst_vif.wait_clks(10);
      check_reset_status('0);
      check_wake_status('0);

      cfg.slow_clk_rst_vif.wait_clks(10);
      // An interrupt will be generated depending on the exact timing of the slow fsm getting
      // the reset and wakeup. We choose not to predict it here (it is checked on other tests).
      // Instead, we just check if the interrupt status is asserted and it is enabled the
      // output interrupt is active.
      check_and_clear_interrupt(.expected(1'b1), .check_expected('0));
      // Clear hardware resets: if they are enabled they are cleared when rst_lc_req[1] goes active,
      // but this makes sure they are cleared even if none is enabled for the next round.
      cfg.pwrmgr_vif.update_resets('0);
      // And make the cpu active.
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b0);
    end
    clear_wake_info();
  endtask

endclass : pwrmgr_wakeup_reset_vseq
