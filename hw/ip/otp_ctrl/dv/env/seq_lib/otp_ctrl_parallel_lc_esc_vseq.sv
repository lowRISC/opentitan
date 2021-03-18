// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will randomly issue lc_escalate_en during or after partition is locked.
// After lc_escalate_en is On, this sequence will continue run base sequence to check if all state
// machines are locked to `ErrorSt`.

class otp_ctrl_parallel_lc_esc_vseq extends otp_ctrl_dai_errs_vseq;
  `uvm_object_utils(otp_ctrl_parallel_lc_esc_vseq)

  `uvm_object_new

  // This sequence will kill super.body sequence once lc_escalate_en is On. Disable these interface
  // requests to avoid sequencer error.
  constraint key_lc_reqs_c {
    do_req_keys == 0;
    do_lc_trans == 0;
  }

  virtual task body();
    fork
      begin : isolation_fork
        fork
          rand_wait_csr_no_outstanding();
          super.body();
        join_any;
        disable fork;
        set_lc_esc_and_check();
      end
    join
  endtask

  virtual task rand_wait_csr_no_outstanding();
    wait(cfg.under_reset == 0);
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10_000));
    wait_no_outstanding_access();
  endtask

  virtual task set_lc_esc_and_check();
    // TODO: random drive any values instead of just on and off
    cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::On);

    // TODO: in alert_esc_monitor, makes it auto-response like push-pull agent
    if (en_auto_alerts_response && cfg.list_of_alerts.size()) run_alert_rsp_seq_nonblocking();

    // Turn off reset because if issuing lc_escalation_en during otp program, scb cannot
    // predict if the OTP memory is programmed or not.
    // TODO: temp disable, support it in stress_all_with_rand_reset case
    do_reset_in_seq = 0;

    // Wait 5 clock cycles until async lc_escalate_en propogate to each state machine.
    cfg.clk_rst_vif.wait_clks(5);

    // After LC_escalate is On, we trigger the dai_errs_vseq to check interfaces will return
    // default values and the design won't hang.
    otp_ctrl_dai_errs_vseq::body();
  endtask

  virtual task post_start();
    // Use reset to clear lc interrupt error
    if (do_apply_reset) begin
      apply_reset();
      cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
    end else wait(0); // wait until upper seq resets and kills this seq

    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
    super.post_start();
  endtask
endclass
