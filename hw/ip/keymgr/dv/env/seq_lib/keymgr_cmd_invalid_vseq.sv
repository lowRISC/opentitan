// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// force design to trigger cmd/state invalid error
// randomly force design FSM/CMD, which causes design behaves very unpredictable
// so, disable the scb and check fatal alert occurs and state is updated correctly after the err
class keymgr_cmd_invalid_vseq extends keymgr_lc_disable_vseq;
  `uvm_object_utils(keymgr_cmd_invalid_vseq)
  `uvm_object_new

  virtual task trigger_error(ref bit regular_vseq_done);
    cfg.en_scb = 0;

    // forcing internal design may cause uninitialized reg to be used, disable these checking
    $assertoff(0, "tb.keymgr_kmac_intf");
    $assertoff(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
    cfg.keymgr_vif.force_cmd_err();

    // if it's in StDisabled, do an OP to ensure fault error occurs
    if (current_state == keymgr_pkg::StDisabled) begin
      wait(regular_vseq_done);
      keymgr_operations(.clr_output(0), .wait_done(0));
    end

    // could not accurately predict when first fatal alert happen, so wait for the first fatal
    // alert to trigger
    wait(cfg.m_alert_agent_cfg["fatal_fault_err"].vif.alert_tx_final.alert_p);
    check_fatal_alert_nonblocking("fatal_fault_err");

    cfg.clk_rst_vif.wait_clks($urandom_range(1, 500));
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_pkg::StDisabled));
  endtask : trigger_error

  // disable checker in seq, only check in scb
  virtual function bit get_check_en();
    return 0;
  endfunction

  task post_start();
    // fatal alert will be triggered, need reset to clear it
    do_reset_at_end_of_seq = 1;
    super.post_start();
    cfg.en_scb = 1;
    $assertoff(1, "tb.keymgr_kmac_intf");
    $assertoff(1, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
  endtask
endclass : keymgr_cmd_invalid_vseq
