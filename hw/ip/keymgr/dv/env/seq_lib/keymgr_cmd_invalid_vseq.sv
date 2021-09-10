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
    bit[TL_DW-1:0] rd_val;
    cfg.en_scb = 0;
    cfg.keymgr_vif.en_chk = 0;

    // forcing internal design may cause uninitialized reg to be used, disable these checking
    $assertoff(0, "tb.keymgr_kmac_intf");
    $assertoff(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
    $assertoff(0, "tb.dut.u_ctrl.DataEn_A");
    $assertoff(0, "tb.dut.u_ctrl.DataEnDis_A");
    $assertoff(0, "tb.dut.u_ctrl.CntZero_A");
    $assertoff(0, "tb.dut.u_kmac_if.LastStrb_A");
    $assertoff(0, "tb.dut.KmacDataKnownO_A");

    cfg.keymgr_vif.force_cmd_err();

    if (!(cfg.keymgr_vif.is_cmd_err && cfg.keymgr_vif.is_kmac_if_fsm_err &&
          cfg.keymgr_vif.is_kmac_if_cnt_err && cfg.keymgr_vif.is_ctrl_fsm_err &&
          cfg.keymgr_vif.is_ctrl_cnt_err)) begin
      // didn't find a right place to force design and no error occurs
      return;
    end

    // wait for 2 cycle to allow design to trigger alert and update fault_status
    cfg.clk_rst_vif.wait_clks(2);

    check_fatal_alert_nonblocking("fatal_fault_err");

    rd_val[keymgr_pkg::FaultKmacCmd] = cfg.keymgr_vif.is_cmd_err;
    rd_val[keymgr_pkg::FaultKmacFsm] = cfg.keymgr_vif.is_kmac_if_fsm_err ||
                                       cfg.keymgr_vif.is_kmac_if_cnt_err;
    rd_val[keymgr_pkg::FaultCtrlFsm] = cfg.keymgr_vif.is_ctrl_fsm_err;
    rd_val[keymgr_pkg::FaultCtrlCnt] = cfg.keymgr_vif.is_ctrl_cnt_err;

    csr_rd_check(.ptr(ral.fault_status), .compare_value(rd_val));

    // if it's in StDisabled, do an OP to ensure fault error occurs
    if (current_state == keymgr_pkg::StDisabled) begin
      keymgr_operations(.clr_output(0), .wait_done(1));
    end else if (current_state == keymgr_pkg::StReset) begin
      // Do an operation to trigger the error. In StReset, only advance is accepted
      keymgr_advance();
    end else begin
      wait_op_done();
    end

    cfg.clk_rst_vif.wait_clks($urandom_range(1, 500));
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_pkg::StInvalid));
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
    cfg.keymgr_vif.en_chk = 1;
    $asserton(0, "tb.keymgr_kmac_intf");
    $asserton(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
    $asserton(0, "tb.dut.u_ctrl.DataEn_A");
    $asserton(0, "tb.dut.u_ctrl.DataEnDis_A");
    $asserton(0, "tb.dut.u_ctrl.CntZero_A");
    $asserton(0, "tb.dut.u_kmac_if.LastStrb_A");
    $asserton(0, "tb.dut.KmacDataKnownO_A");
  endtask
endclass : keymgr_cmd_invalid_vseq
