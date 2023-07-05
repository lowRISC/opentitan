// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// The reset test randomly introduces external resets.
class pwrmgr_sw_reset_vseq extends pwrmgr_base_vseq;

  `uvm_object_utils(pwrmgr_sw_reset_vseq)
  `uvm_object_new

  constraint wakeups_c {wakeups == 0;}
  constraint wakeups_en_c {wakeups_en == 0;}

  task body();
    int exp_rst;
    wait_for_fast_fsm_active();

    check_reset_status('0);
    num_trans_c.constraint_mode(0);
    num_trans = 30;
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));

      cfg.pwrmgr_vif.sw_rst_req_i = prim_mubi_pkg::mubi4_t'($urandom_range(0, 15));
      exp_rst = (cfg.pwrmgr_vif.sw_rst_req_i == prim_mubi_pkg::MuBi4True);
      cfg.slow_clk_rst_vif.wait_clks(4);

      // sw reset causes fast state machine transition to lowpower state
      if (exp_rst == 1) begin
        `DV_SPINWAIT(wait(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive);,
                     "timeout waiting for non fast-active state", 1000)
      end

      // This read is not always possible since the CPU may be off.

      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from reset", UVM_MEDIUM)

      check_wake_info(.reasons('0), .fall_through(1'b0), .abort(1'b0));

      cfg.slow_clk_rst_vif.wait_clks(4);
      check_reset_status('0);

      // And check interrupt is not set.
      check_and_clear_interrupt(.expected(1'b0));
    end
    clear_wake_info();
  endtask

endclass : pwrmgr_sw_reset_vseq
