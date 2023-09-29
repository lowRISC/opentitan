// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Description:
// This sequence creates escalation clock and reset malfunction at FastPwrStateActive state.
// This event will trigger timeout counter and assert timeout signal
// when timeout counter reaches EscTimeOutCnt value.
// Once the timeout occurs, it will create fatal alert and alert agent(tb) will set esc rst.
// The pass or failure status is determined in the cip scoreboard.
class pwrmgr_esc_clk_rst_malfunc_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_esc_clk_rst_malfunc_vseq)

  `uvm_object_new
  constraint num_trans_c {num_trans inside {[1 : 3]};}

  virtual task body();
    wait_for_fast_fsm_active();
    // Wait some time so the stimulus is sent after the fast fsm becoming active.
    cfg.clk_rst_vif.wait_clks(4);
    expect_fatal_alerts = 1;
    trigger_escalation_timeout();
    wait_for_fast_fsm_active();
  endtask : body

  // Trigers an escalation timeout fault, either stopping clk_esc_i or driving rst_esc_ni.
  //
  // Randomly set a bit to 0 or 1: if 0 stop clk_esc_i, if 1 make rst_esc_ni active.
  task trigger_escalation_timeout();
    int which = $urandom_range(0, 1);
    `uvm_info(`gfn, $sformatf("Triggering escalation via %0s", which ? "rst" : "clk"), UVM_MEDIUM)
    if (which == 0) cfg.esc_clk_rst_vif.stop_clk();
    else cfg.esc_clk_rst_vif.drive_rst_pin(1'b0);

    // Wait for cpu fetch to be disabled, as an indication a reset is triggered.
    `DV_SPINWAIT(wait (cfg.pwrmgr_vif.fetch_en != lc_ctrl_pkg::On);,
                 "timeout waiting for the CPU to be inactive", FetchEnTimeoutNs)
    `uvm_info(`gfn, "Releasing trigger", UVM_MEDIUM)
    if (which == 0) cfg.esc_clk_rst_vif.start_clk();
    else cfg.esc_clk_rst_vif.drive_rst_pin(1'b1);
  endtask : trigger_escalation_timeout
endclass
