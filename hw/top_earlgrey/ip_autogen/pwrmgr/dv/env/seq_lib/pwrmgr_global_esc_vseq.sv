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
      repeat (cycle) @(cfg.clk_rst_vif.cb);
      clear_escalation_reset();
    end
  endtask : send_esc

  task check_rst_req();
    bit dut_init_done = -1;

    while (trans_cnt < num_trans) begin
      @(cfg.clk_rst_vif.cb);
      wait(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive &&
           cfg.pwrmgr_vif.pwr_rst_req.rstreqs[3] == 1'b1);
      trans_cnt++;

      // Make sure previous dut_init is done
      if (dut_init_done > -1) begin
        wait(dut_init_done == 1);
      end
      // Spawning dut_init thread then go to
      // wait reset state
      fork
        begin
          dut_init_done = 0;
          dut_init();
          dut_init_done = 1;
        end
        begin
          cfg.clk_rst_vif.wait_clks(10);
        end
      join_any
    end
    wait(dut_init_done == 1);
  endtask : check_rst_req

endclass
