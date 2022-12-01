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

    // send a expected alert to the scoreboard
    expect_fatal_alerts = 1;
    enqueue_exp_alert();

    // esc [clk|rst] malfunction
    add_noise();

    // Expect to start reset.
    `DV_WAIT(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive)
    `uvm_info(`gfn, "Started to process reset", UVM_MEDIUM)

    // For the cip scoreboard.
    reset_start_for_cip();

    // clear to end test gracfully
    clear_noise();

    wait_for_fast_fsm_active();
    `uvm_info(`gfn, "Back from reset", UVM_MEDIUM)
    // For the cip scoreboard.
    reset_end_for_cip();

  endtask : body

  task add_noise();
    int delay = $urandom_range(10, 30);
    string path;
    randcase
      1: path = "tb.dut.rst_esc_ni";
      1: path = "tb.dut.clk_esc_i";
    endcase
    `uvm_info(`gfn, $sformatf("Sending noise via %s", path), UVM_MEDIUM)
    `DV_CHECK(uvm_hdl_force(path, 0))
    #(delay * 1us);
  endtask : add_noise

  task clear_noise();
    int delay = $urandom_range(1, 5);
    string path;
    `uvm_info(`gfn, "Releasing noise", UVM_MEDIUM)
    path = "tb.dut.rst_esc_ni";
    `DV_CHECK(uvm_hdl_release(path))
    path = "tb.dut.clk_esc_i";
    `DV_CHECK(uvm_hdl_release(path))
    #(delay * 100ns);
  endtask : clear_noise
endclass
