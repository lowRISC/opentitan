// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This simple sequence checks if the background check can be triggered once the period is set.

class otp_ctrl_background_chks_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_background_chks_vseq)

  `uvm_object_new

  rand bit [1:0] trigger_chks;
  rand uint      check_period;

  constraint regwens_c {check_regwen_val == 1;}

  // At least one check will be triggered
  constraint check_triggers_c {trigger_chks > 0;}

  constraint check_period_c {
    check_period < 20;
    check_period > 0;
  }

  task body();
    int check_wait_cycles;
    super.body();

    // For stress_all_with_rand_reset test, if previous lc_esc_en is not cleared, then skip the
    // background check.
    if (cfg.otp_ctrl_vif.lc_esc_on == 0) begin

      // Write background check
      if (trigger_chks[0]) csr_wr(ral.integrity_check_period,   check_period);
      if (trigger_chks[1]) csr_wr(ral.consistency_check_period, check_period);
      `uvm_info(`gfn, $sformatf("trigger background check %0h", trigger_chks), UVM_LOW)

      cfg.en_scb = 0;
      // According to spec, check period will append an 'hFF from the LSF. Add 10 cycle buffers for
      // register updates.
      check_wait_cycles = (check_period + 1) << 8 + 10;

      // Wait for first check done
      repeat($countones(trigger_chks)) begin
        csr_spinwait(.ptr(ral.status.check_pending), .exp_data(1),
                     .timeout_ns(cfg.clk_rst_vif.clk_period_ps / 1000 * check_wait_cycles));

        csr_spinwait(.ptr(ral.status.check_pending), .exp_data(0));
      end

      // Configure timeout settings to trigger check error
      csr_wr(ral.check_timeout, $urandom_range(1, 5));
      `uvm_info(`gfn, "trigger check timeout error", UVM_LOW)

      // Wait for fatal alert
      `DV_SPINWAIT_EXIT(
         wait(cfg.m_alert_agent_cfgs["fatal_check_error"].vif.alert_tx_final.alert_p);,
         cfg.clk_rst_vif.wait_clks(check_wait_cycles);,
         $sformatf("Timeout waiting for alert %0s", "fatal_check_error"))
      check_fatal_alert_nonblocking("fatal_check_error");

      cfg.clk_rst_vif.wait_clks($urandom_range(50, 1000));
      csr_rd_check(.ptr(ral.status.timeout_error), .compare_value(1));
    end
  endtask

  // Enable scoreboard is done in stress_all sequence and `apply_resets_concurrently` task to
  // avoid otp_ctrl_scoreboard reporting failures when reset has not been issued.
  virtual task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask
endclass
