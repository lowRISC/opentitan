// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The smoke test brings the pwrmgr through a POR reset, followed by a low
// power sequence, followed by reset.

// smoke test vseq
class pwrmgr_smoke_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_smoke_vseq)

  `uvm_object_new
  constraint cycles_before_rst_lc_src_c {cycles_before_rst_lc_src inside {[1 : 2]};}
  constraint cycles_before_otp_done_c {cycles_before_otp_done inside {[1 : 2]};}
  constraint cycles_before_lc_done_c {cycles_before_lc_done inside {[1 : 2]};}

  constraint wakeups_c {wakeups != 0;}
  constraint resets_c {resets != 0;}

  task body();
    logic [TL_DW-1:0] value;
    wakeups_t wakeup_en;
    resets_t reset_en;
    set_nvms_idle();
    setup_interrupt(.enable(1'b1));
    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(0));
    csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0));

    // Enable all wakeups so a peripheral can cause a wakeup.
    wakeup_en = '1;
    csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeup_en));
    wait_for_csr_to_propagate_to_slow_domain();
    `uvm_info(`gfn, "smoke waiting for wakeup propagate", UVM_MEDIUM)

    // Initiate low power transition.
    csr_wr(.ptr(ral.control.low_power_hint), .value(1'b1));
    cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
    if (ral.control.main_pd_n.get_mirrored_value() == 1'b0) begin
      wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);
    end

    // Now bring it back.
    cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
    cfg.pwrmgr_vif.update_wakeups(wakeups);

    wait_for_fast_fsm_active();
    `uvm_info(`gfn, "smoke back from wakeup", UVM_MEDIUM)

    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(wakeups & wakeup_en),
                 .err_msg("failed wake_status check"));
    csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0),
                 .err_msg("failed reset_status check"));
    check_and_clear_interrupt(.expected(1'b1));

    // Enable resets.
    reset_en = '1;
    csr_wr(.ptr(ral.reset_en[0]), .value(reset_en));
    wait_for_csr_to_propagate_to_slow_domain();

    // Trigger a reset.
    cfg.pwrmgr_vif.update_resets(resets);
    cfg.slow_clk_rst_vif.wait_clks(2);
    wait_for_reset_cause(pwrmgr_pkg::HwReq);

    // Now bring it back: the slow fsm doesn't participate on this, so we cannot
    // rely on the ctrl_cfg_regwen CSR. Wait for the reset status to clear.
    wait_for_fast_fsm_active();

    // The reset_status CSR should be clear since the unit requesting reset
    // should have been reset, so the incoming reset should have cleared.
    csr_rd_check(.ptr(ral.reset_status[0]), .compare_value('0));

    // Wait for interrupt to be generated whether or not it is enabled.
    cfg.slow_clk_rst_vif.wait_clks(10);
    check_and_clear_interrupt(.expected(1'b0));
  endtask

endclass : pwrmgr_smoke_vseq
