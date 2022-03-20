// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// This sequence creates escalation clock and reset malfunction at FastPwrStateActive state.
// This event will trigger timeout counter and assert timeout signal
// when timeout counter reaches EscTimeOutCnt value.
// Once the timeout occurs, it will create fatal alert and alert agent(tb) will set esc rst.
class pwrmgr_esc_clk_rst_malfunc_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_esc_clk_rst_malfunc_vseq)

  `uvm_object_new
  constraint num_trans_c {num_trans inside {[1 : 3]};}

  virtual task body();
    int margin = $urandom_range(0,10);
    // before body, fast state become active state
    // Add some time margin after fsm become active state.
    #(margin * 1ns);

    // send a expected alert to the scoreboard
    expect_fatal_alerts = 1;
    cfg.exp_alert_q.push_back(1);

    // esc [clk|rst] malfunction
    add_noise();

    // clear to end test gracfully
    clear_noise();
  endtask : body

  task add_noise();
    int delay = $urandom_range(10,30);

    randcase
      1:void'(uvm_hdl_force("tb.dut.rst_esc_ni", 0));
      1:void'(uvm_hdl_force("tb.dut.clk_esc_i", 0));
    endcase // randcase
    #(delay * 1us);
  endtask // add_noise

  task clear_noise();
    int delay = $urandom_range(1,5);
    void'(uvm_hdl_release("tb.dut.rst_esc_ni"));
    void'(uvm_hdl_release("tb.dut.clk_esc_i"));
    #(delay * 100ns);
  endtask // clear_noise
endclass
