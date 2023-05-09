// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trigger ErrWaitTimerExpired error by setting edn timeout to a very small value.
// This sequence will check:
// - Kmac error interrupt is set via check_err() task.
// - Kmac output correct err_code.
// - Kmac can finish the operation without hanging.
// - Check error bit in keymgr app interface.
class kmac_edn_timeout_error_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_edn_timeout_error_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:20]};
  }

  constraint kmac_err_type_c {
    kmac_err_type dist {kmac_pkg::ErrWaitTimerExpired :/ 9, kmac_pkg::ErrNone :/ 1};
    kmac_err_type == kmac_pkg::ErrWaitTimerExpired -> entropy_fast_process == 0;
  }

  function void pre_randomize();
    this.disable_err_c.constraint_mode(0);
    this.en_app_c.constraint_mode(0);
  endfunction

  virtual task pre_start();
    super.pre_start();
    if (cfg.enable_masking) disable_asserts();
    cfg.en_scb = 0;
    check_keymgr_rsp_nonblocking();
    kmac_err_type.rand_mode(0);
  endtask

  virtual function void disable_asserts();
    $assertoff(0,
      "tb.dut.gen_entropy.u_prim_sync_reqack_data.u_prim_sync_reqack.SyncReqAckAckNeedsReq");
    $assertoff(0, "tb.edn_if[0].ReqHighUntilAck_A");
    $assertoff(0, "tb.edn_if[0].AckAssertedOnlyWhenReqAsserted_A");
  endfunction

  virtual task post_start();
    super.post_start();

    // ICEBOX: enable scb and run normal sequence, then add this sequence to stress_all sequence.
    // cfg.en_scb = 1;
  endtask

  // Because scb is disabled, use sequence to check if `err_code` is correct.
  virtual task check_err(bit clear_err = 1'b1);
    super.check_err(clear_err);
    check_err_code();
  endtask

  virtual task check_err_code();
    kmac_pkg::err_t kmac_err = '{valid: 1'b1,
                                 code: kmac_pkg::ErrWaitTimerExpired,
                                 info: '0};
    csr_rd_check(.ptr(ral.err_code), .compare_value(kmac_err));
  endtask

  virtual task check_keymgr_rsp_nonblocking();
    fork begin
      while (cfg.en_scb == 0 && entropy_fetched == 0) begin
        wait (cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.kmac_data_rsp.done == 1);
        if (cfg.enable_masking && entropy_mode == EntropyModeEdn) begin
          `DV_CHECK_EQ(cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.kmac_data_rsp.error, 1)
        end
        wait (cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.kmac_data_rsp.done == 0);
      end
    end join_none
  endtask

endclass
