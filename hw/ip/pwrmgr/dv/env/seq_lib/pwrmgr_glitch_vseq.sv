// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class pwrmgr_glitch_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_glitch_vseq)

  `uvm_object_new

  int trans_cnt = 0;
  constraint num_trans_c {num_trans inside {[1 : 5]};}

  virtual task body();
    for (int i = 0; i < num_trans; ++i) begin
      wait_for_fast_fsm_active();
      cfg.pwrmgr_vif.glitch_power_reset();
      cfg.clk_rst_vif.wait_clks(cycles_before_reset);
      fork begin
        fork
          begin
            wait(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateResetPrep &&
                 cfg.pwrmgr_vif.pwr_rst_req.rstreqs[2] == 1);
            dut_init();
          end
          begin
            #10us;
            `uvm_error(`gfn,
                       $sformatf("checker timeout : fast_state %s, pwr_rst_req 0x%x",
                                 cfg.pwrmgr_vif.fast_state.name,
                                 cfg.pwrmgr_vif.pwr_rst_req.rstreqs))
          end
        join_any
        disable fork;
      end join
    end
  endtask : body
endclass
