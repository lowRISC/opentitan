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

  constraint control_enables_c {
    control_enables.core_clk_en == ral.control.core_clk_en.get_reset();
    control_enables.io_clk_en == ral.control.io_clk_en.get_reset();
    control_enables.usb_clk_en_lp == ral.control.usb_clk_en_lp.get_reset();
    control_enables.usb_clk_en_active == ral.control.usb_clk_en_active.get_reset();
    control_enables.main_pd_n == ral.control.main_pd_n.get_reset();
  }

  task body();
    logic [TL_DW-1:0] value;
    wakeups_t wakeup_en;
    resets_t reset_en;
    wait_for_fast_fsm_active();
    set_nvms_idle();
    setup_interrupt(.enable(1'b1));

    check_wake_status('0);
    check_reset_status('0);

    // Enable all wakeups so any peripheral can cause a wakeup.
    wakeup_en = '1;
    csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeup_en));
    low_power_hint = 1'b1;
    update_control_csr();
    wait_for_csr_to_propagate_to_slow_domain();

    // Initiate low power transition.
    cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
    wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);

    // Now bring it back.
    cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
    cfg.pwrmgr_vif.update_wakeups(wakeups);

    wait_for_fast_fsm_active();
    `uvm_info(`gfn, "smoke back from wakeup", UVM_MEDIUM)

    check_wake_status(wakeups & wakeup_en);
    check_reset_status('0);
    // And make the cpu active.
    cfg.pwrmgr_vif.update_cpu_sleeping(1'b0);

    cfg.pwrmgr_vif.update_wakeups('0);
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
    check_reset_status('0);
    check_wake_status('0);
    clear_wake_info();

    // Wait for interrupt to be generated whether or not it is enabled.
    cfg.slow_clk_rst_vif.wait_clks(10);
    check_and_clear_interrupt(.expected(1'b0));
  endtask

endclass : pwrmgr_smoke_vseq
