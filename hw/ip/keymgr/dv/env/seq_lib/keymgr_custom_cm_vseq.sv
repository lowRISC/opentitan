// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// force design to trigger cmd/state invalid error
// randomly force design FSM/CMD, which causes design to behave very unpredictable
// so, disable the scb and check fatal alert occurs and state is updated correctly after the err
class keymgr_custom_cm_vseq extends keymgr_lc_disable_vseq;
  `uvm_object_utils(keymgr_custom_cm_vseq)
  `uvm_object_new

  // override the constrant - don't need to always advance to StDisabled
  constraint num_adv_c {
    num_adv inside {[1:state.num()]};
  }
  rand keymgr_fault_inject_type_e fi_type;

  virtual task trigger_error(ref bit regular_vseq_done);
    keymgr_pkg::keymgr_op_status_e op_status;
    cfg.en_scb = 0;
    cfg.keymgr_vif.en_chk = 0;
    // scb is off for this test. Enable CSR auto_predict, otherwise, csr_update doesn't work
    // correctly as `needs_update` may be wrong due to the incorrect mirrored value.
    ral.default_map.set_auto_predict(1);

    // forcing internal design may cause uninitialized reg to be used, disable these checking
    $assertoff(0, "tb.keymgr_kmac_intf");
    $assertoff(0, "tb.dut.u_ctrl.DataEn_A");
    $assertoff(0, "tb.dut.u_ctrl.DataEnDis_A");
    $assertoff(0, "tb.dut.u_ctrl.CntZero_A");
    $assertoff(0, "tb.dut.u_kmac_if.LastStrb_A");
    $assertoff(0, "tb.dut.KmacDataKnownO_A");

    // these 2 fault needs to be issued during an operation, wait until main test is done,
    // then issue an operation.
    if (fi_type == FaultOpNotConsistent) begin
      `DV_WAIT(regular_vseq_done)
      issue_a_random_op(.wait_done(0));
    end else if (fi_type == FaultSideloadNotConsistent) begin
      `DV_WAIT(regular_vseq_done)
      csr_wr(.ptr(ral.sideload_clear), .value('1));
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(key_dest, key_dest != keymgr_pkg::None;)
      keymgr_generate(.operation(keymgr_pkg::OpGenHwOut), .key_dest(key_dest), .wait_done(0));
    end else if (fi_type == FaultOpNotExist) begin
      `DV_WAIT(regular_vseq_done)
      // SW sets no valid operation, then force operation happens internally to trigger an error.
      ral.control_shadowed.operation.set(keymgr_pkg::OpDisable);
      csr_update(ral.control_shadowed);
    end
    cfg.keymgr_vif.inject_fault(fi_type);

    // wait for a few cycles to allow design to trigger alert and update fault_status.
    cfg.clk_rst_vif.wait_clks(3);

    check_fatal_alert_nonblocking("fatal_fault_err");

    case (fi_type)
      FaultOpNotOnehot, FaultOpNotConsistent: begin
        csr_rd_check(.ptr(ral.fault_status.cmd), .compare_value(1));
        if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultKmacCmd);
      end
      FaultKmacDoneError: begin
        csr_rd_check(.ptr(ral.fault_status.kmac_done), .compare_value(1));
        if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultKmacDone);
      end
      FaultOpNotExist: begin
        csr_rd_check(.ptr(ral.fault_status.ctrl_fsm_chk), .compare_value(1));
        if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultCtrlFsmChk);
      end
      FaultSideloadNotConsistent: begin
        csr_rd_check(.ptr(ral.fault_status.side_ctrl_sel), .compare_value(1));
        if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultSideSel);
      end
      FaultKeyIntgError: begin
        csr_rd_check(.ptr(ral.fault_status.key_ecc), .compare_value(1));
        if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultKeyEcc);
      end
      default: `uvm_fatal(`gfn, "impossible value")
    endcase

    `DV_WAIT(regular_vseq_done)
    // in case that OP is WIP, status may not enter StInvalid, wait until this OP is done.
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpWip),
                 .compare_op(CompareOpNe));
    check_after_fi();
  endtask : trigger_error

  // disable checker in seq, only check in scb
  virtual function bit get_check_en();
    return 0;
  endfunction

  task post_start();
    // fatal alert will be triggered, need reset to clear it
    expect_fatal_alerts = 1;
    super.post_start();
    $asserton(0, "tb.keymgr_kmac_intf");
    $asserton(0, "tb.dut.u_ctrl.DataEn_A");
    $asserton(0, "tb.dut.u_ctrl.DataEnDis_A");
    $asserton(0, "tb.dut.u_ctrl.CntZero_A");
    $asserton(0, "tb.dut.u_kmac_if.LastStrb_A");
    $asserton(0, "tb.dut.KmacDataKnownO_A");
  endtask
endclass : keymgr_custom_cm_vseq
