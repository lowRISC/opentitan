// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test multiple resets with setting lc_* inputs with random value.
class pwrmgr_disable_rom_integrity_check_vseq extends pwrmgr_base_vseq;

  `uvm_object_utils(pwrmgr_disable_rom_integrity_check_vseq)
  `uvm_object_new

  constraint wakeups_c {wakeups == 0;}
  constraint wakeups_en_c {wakeups_en == 0;}

  function void post_randomize();
    sw_rst_from_rstmgr = get_rand_mubi4_val(8, 4, 4);
    super.post_randomize();
  endfunction

  task body();
    resets_t enabled_resets;
    wait_for_fast_fsm_active();
    check_reset_status('0);

    for (int i = 0; i < 5; ++i) begin
      `uvm_info(`gfn, $sformatf("Starting new round%0d", i), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));

      // set lc ctrl input to random value
      cfg.pwrmgr_vif.lc_hw_debug_en = get_rand_lc_tx_val(
          .t_weight(0), .f_weight(1), .other_weight(4)
      );
      cfg.pwrmgr_vif.lc_dft_en = get_rand_lc_tx_val(.t_weight(0), .f_weight(1), .other_weight(4));
      cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
      cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
      `uvm_info(`gfn, "Set done True, good False", UVM_MEDIUM)
      enabled_resets = resets_en & resets;
      `uvm_info(`gfn, $sformatf(
                "Enabled resets=0x%x, power_reset=%b, escalation=%b, sw_reset=%b",
                enabled_resets,
                power_glitch_reset,
                escalation_reset,
                sw_rst_from_rstmgr
                ), UVM_MEDIUM)

      csr_wr(.ptr(ral.reset_en[0]), .value(resets_en));
      // This is necessary to propagate reset_en.
      wait_for_csr_to_propagate_to_slow_domain();

      // Trigger resets. The glitch is sent prior to the externals since if it is delayed
      // it will cause a separate reset after the externals, which complicates the checks.
      if (power_glitch_reset) begin
        `uvm_info(`gfn, "Sending power glitch", UVM_MEDIUM)
        // expected alerts
        expect_fatal_alerts = 1;
        cfg.exp_alert_q.push_back(1);
        cfg.pwrmgr_vif.glitch_power_reset();
      end
      cfg.clk_rst_vif.wait_clks(cycles_before_reset);

      if (cycles_before_reset == 0) enabled_resets = 0;

      `uvm_info(`gfn, $sformatf("Sending resets=0x%x", resets), UVM_MEDIUM)
      cfg.pwrmgr_vif.update_resets(resets);
      `uvm_info(`gfn, $sformatf("Sending sw reset from rstmgr=%b", sw_rst_from_rstmgr), UVM_MEDIUM)
      if (escalation_reset) send_escalation_reset();
      cfg.pwrmgr_vif.update_sw_rst_req(sw_rst_from_rstmgr);

      `uvm_info(`gfn, "Wait for Fast State NE FastPwrStateActive", UVM_MEDIUM)
      `DV_WAIT(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive)

      // For the cip scoreboard.
      reset_start_for_cip();

      // Check fast state is not FastPwrStateActive for a while
      repeat (20) begin
        @cfg.slow_clk_rst_vif.cb;
        `DV_CHECK_NE(cfg.pwrmgr_vif.fast_state, pwrmgr_pkg::FastPwrStateActive)
      end

      `uvm_info(`gfn, "Set lc ctrl input On", UVM_MEDIUM)
      cfg.pwrmgr_vif.lc_hw_debug_en = lc_ctrl_pkg::On;
      cfg.pwrmgr_vif.lc_dft_en = lc_ctrl_pkg::On;

      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from reset", UVM_MEDIUM)

      // For the cip scoreboard.
      reset_end_for_cip();

      check_wake_info(.reasons('0), .fall_through(1'b0), .abort(1'b0));

      cfg.slow_clk_rst_vif.wait_clks(4);
      check_reset_status('0);

      // And check interrupt is not set.
      check_and_clear_interrupt(.expected(1'b0));
    end
    clear_wake_info();
  endtask

endclass : pwrmgr_disable_rom_integrity_check_vseq
