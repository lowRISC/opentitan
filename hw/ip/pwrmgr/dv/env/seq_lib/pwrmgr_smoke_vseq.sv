// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The smoke test brings the pwrmgr through a POR reset, followed by a low
// power sequence, followed by reset.

// smoke test vseq
class pwrmgr_smoke_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_smoke_vseq)

  `uvm_object_new
  constraint cycles_before_rst_lc_src_c { cycles_before_rst_lc_src inside {[1:2]}; }
  constraint cycles_before_otp_done_c { cycles_before_otp_done inside {[1:2]}; }
  constraint cycles_before_lc_done_c { cycles_before_lc_done inside {[1:2]}; }

  rand bit [pwrmgr_reg_pkg::NumWkups-1:0] wakeups;
  rand bit [pwrmgr_reg_pkg::NumRstReqs-1:0] resets;

  constraint wakeups_c { wakeups != 0; }
  constraint resets_c { resets != 0; }

  task wait_for_reset_cause(pwrmgr_pkg::reset_cause_e cause);
    wait (cfg.pwrmgr_vif.pwr_rst_req.reset_cause == cause);
    `uvm_info(`gfn, $sformatf("Observed reset cause_match 0x%x", cause), UVM_MEDIUM)
  endtask

  task body();
    logic [TL_DW-1:0] value;
    bit [pwrmgr_reg_pkg::NumWkups-1:0] wakeup_en;
    bit [pwrmgr_reg_pkg::NumRstReqs-1:0] reset_en;
    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    start_slow_fsm();
    start_fast_from_low_power();
    cfg.slow_clk_rst_vif.wait_clks(10);

    wait_for_fast_fsm_active();
    csr_rd_check(.ptr(ral.wake_status), .compare_value(0));
    csr_rd_check(.ptr(ral.reset_status), .compare_value(0));

    // Enable all wakeups so a peripheral can cause a wakeup.
    wakeup_en = '1;
    csr_wr(.ptr(ral.wakeup_en), .value(wakeup_en));
    wait_for_csr_to_propagate_to_slow_domain();

    // Initiate low power transition.
    csr_wr(.ptr(ral.control.low_power_hint), .value(1'b1));
    cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
    fast_to_low_power();
    turn_clocks_off_for_slow_to_low_power();
    wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);

    // Now bring it back.
    cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
    cfg.pwrmgr_vif.update_wakeups(wakeups);

    start_slow_fsm();
    start_fast_from_low_power();
    cfg.slow_clk_rst_vif.wait_clks(10);

    wait_for_fast_fsm_active();

    csr_rd_check(.ptr(ral.wake_status), .compare_value(wakeups & wakeup_en));
    csr_rd_check(.ptr(ral.reset_status), .compare_value(0));

    // Enable resets.
    reset_en = '1;
    csr_wr(.ptr(ral.reset_en), .value(reset_en));
    wait_for_csr_to_propagate_to_slow_domain();

    // Trigger a reset.
    cfg.pwrmgr_vif.update_resets(resets);
    cfg.slow_clk_rst_vif.wait_clks(2);
    fast_to_low_power();
    wait_for_reset_cause(pwrmgr_pkg::HwReq);

    // Now bring it back: the slow fsm doesn't participate on this.
    assert_rstmgr_resets();
    start_fast_from_low_power();
    cfg.slow_clk_rst_vif.wait_clks(10);

    csr_rd_check(.ptr(ral.wake_status), .compare_value(wakeups & wakeup_en));
    csr_rd_check(.ptr(ral.reset_status), .compare_value(resets & reset_en));
  endtask

endclass : pwrmgr_smoke_vseq
