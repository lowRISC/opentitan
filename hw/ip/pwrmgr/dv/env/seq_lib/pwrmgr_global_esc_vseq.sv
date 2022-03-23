// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// This test asserts global escalation reset to dut
// and check glocal escalation request is handled by
// dut properly.
class pwrmgr_global_esc_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_global_esc_vseq)

  `uvm_object_new

  int trans_cnt = 0;
  constraint num_trans_c {num_trans inside {[1 : 5]};}

  virtual task body();
    fork
      send_esc();
      check_rst_req();
    join
  endtask : body

  task send_esc();
    int cycle;
    for (int i = 0; i < num_trans; ++i) begin
      wait_for_fast_fsm_active();
      cycle = $urandom_range(50, 300);
      send_escalation_reset();
      repeat(cycle) @(cfg.clk_rst_vif.cb);
      clear_escalation_reset();
    end
  endtask // send_esc

  task check_rst_req();
    while(trans_cnt < num_trans) begin
      @(cfg.clk_rst_vif.cb);
      wait(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateResetPrep &&
           cfg.pwrmgr_vif.pwr_rst_req.rstreqs == 4'h8);

      trans_cnt++;
      dut_init();
    end
  endtask // check_rst_req

endclass
