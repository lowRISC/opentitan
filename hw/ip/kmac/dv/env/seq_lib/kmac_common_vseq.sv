// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_common_vseq extends kmac_base_vseq;
  `uvm_object_utils(kmac_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_kmac_init = 1'b0;
    entropy_mode_c.constraint_mode(0);
    super.pre_start();

    if (common_seq_type inside {"shadow_reg_errors", "shadow_reg_errors_with_csr_rw"}) begin
      csr_excl_item csr_excl = ral.get_excl_item();
      // Shadow storage fatal error might cause req to drop without ack.
      $assertoff(0,
      "tb.dut.gen_entropy.u_prim_sync_reqack_data.u_prim_sync_reqack.SyncReqAckHoldReq");
      $assertoff(0,
      "tb.dut.gen_entropy.u_prim_sync_reqack_data.u_prim_sync_reqack.SyncReqAckAckNeedsReq");
      $assertoff(0, "tb.edn_if[0].ReqHighUntilAck_A");
      $assertoff(0, "tb.edn_if[0].AckAssertedOnlyWhenReqAsserted_A");
    end
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual function void predict_shadow_reg_status(bit predict_update_err  = 0,
                                                  bit predict_storage_err = 0);
    super.predict_shadow_reg_status(predict_update_err, predict_storage_err);

    if (predict_storage_err) begin
      // For storage error, the kmac `cfg_regwen` register will be set to 0 internally to lock all
      // cfg related CSRs. Because it is a `RO` register, the logic below manually locks the write
      // access for its lockable register fields. (If the regwen is `W0C` access policy, the
      // lockable fields will be updated automatically in `do_predict` function)
      ral.cfg_regwen.en.set_lockable_flds_access(.lock(1));
    end
  endfunction

  // cfg_shadowed register field err_process will clear shadow reg update error.
  virtual task shadow_reg_wr(dv_base_reg    csr,
                             uvm_reg_data_t wdata,
                             bit            en_shadow_wr = 1,
                             bit            predict = 1);
    super.shadow_reg_wr(csr, wdata, en_shadow_wr, predict);
    if (csr.get_name() == "cfg_shadowed") begin
      // If `cfg_shadowed` register is written successfully, then check if update error status
      // will be cleared by `KmacErrProcessed` field.
      if (csr.is_staged() == 0 &&
          csr.get_shadow_update_err() == 0 &&
          csr.get_shadow_storage_err() == 0) begin
        if (wdata[KmacErrProcessed]) clear_update_err_status();
      end
    end
  endtask

  virtual task check_tl_intg_error_response();
    // For tl integrity fatal error, the kmac `cfg_regwen` register will be set to 0 internally to
    // lock all cfg related CSRs. Because it is a `RO` register, the logic below manually locks the
    // write access for its lockable register fields. (If the regwen is `W0C` access policy, the
    // lockable fields will be updated automatically in `do_predict` function)
    ral.cfg_regwen.en.set_lockable_flds_access(.lock(1));
    super.check_tl_intg_error_response();
  endtask

endclass
