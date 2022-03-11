// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trigger both sync and async fault, then check fatal alert is triggered and fault_status is
// updated correctly
class keymgr_sync_async_fault_cross_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_sync_async_fault_cross_vseq)
  `uvm_object_new

  bit sync_fault_trig_first;
  bit async_fault_trig_first;

  task body();
    bit [TL_DW-1:0] act_fault_status;
    keymgr_pkg::keymgr_working_state_e state;

    // At least, advance to StInit, so that keymgr can send data to KMAC to trigger sync fault
    repeat ($urandom_range(1, 4)) keymgr_operations(.advance_state(1));
    cfg.en_scb = 0;
    cfg.keymgr_vif.en_chk = 0;

    // disable push-pull interface assertion since faults may cause the kmac interface
    // to be filled with random, constantly changing data
    $assertoff(0, "tb.keymgr_kmac_intf.req_data_if.H_DataStableWhenValidAndNotReady_A");

    fork
      trigger_sync_fault();
      trigger_async_fault();
    join

    wait_and_check_fatal_alert();

    // Check fault_status
    csr_rd(.ptr(ral.fault_status), .value(act_fault_status));
    `DV_CHECK_EQ(act_fault_status[keymgr_pkg::FaultRegIntg], 1)
    // KMAC output error triggers either one of these 2 errors.
    `DV_CHECK_EQ(act_fault_status[keymgr_pkg::FaultKmacOp] ||
                 act_fault_status[keymgr_pkg::FaultKmacOut], 1)

    if (cfg.en_cov) begin
      cov.sync_async_fault_cross_cg.sample(sync_fault_trig_first, async_fault_trig_first);
    end
  endtask : body

  task trigger_sync_fault();
    // Issue one operation, either advance or gen-out
    bit is_adv_op = $urandom_range(0, 1);

    cfg.m_keymgr_kmac_agent_cfg.error_rsp_pct = 100;
    keymgr_operations(.advance_state(is_adv_op),
                      .num_gen_op(!is_adv_op),
                      .clr_output(0),
                      .wait_done(1));

    if (!async_fault_trig_first) sync_fault_trig_first = 1;
  endtask : trigger_sync_fault

  task trigger_async_fault();
    set_tl_assert_en(.enable(0));

    cfg.clk_rst_vif.wait_clks($urandom_range(0, 2000));
    issue_tl_access_w_intg_err(ral.get_name());
    set_tl_assert_en(.enable(1));

    if (!sync_fault_trig_first) async_fault_trig_first = 1;
  endtask : trigger_async_fault

  // disable checker in base seq, only check in this seq
  virtual function bit get_check_en();
    return 0;
  endfunction

  task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
    cfg.en_scb = 1;
    cfg.keymgr_vif.en_chk = 1;
  endtask

endclass : keymgr_sync_async_fault_cross_vseq
