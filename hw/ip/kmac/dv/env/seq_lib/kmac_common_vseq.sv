// Copyright lowRISC contributors (OpenTitan project).
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

  virtual task check_tl_intg_error_response();
    // For tl integrity fatal error, the kmac `cfg_regwen` register will be set to 0 internally to
    // lock all cfg related CSRs. Because it is a `RO` register, the logic below manually locks the
    // write access for its lockable register fields. (If the regwen is `W0C` access policy, the
    // lockable fields will be updated automatically in `do_predict` function)
    ral.cfg_regwen.en.set_lockable_flds_access(.lock(1));
    super.check_tl_intg_error_response();
  endtask

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    super.check_sec_cm_fi_resp(if_proxy);
    kmac_app_lock_check();
    kmac_sw_lock_check();
  endtask

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (!uvm_re_match("*.u_sha3.u_state_regs*", if_proxy.path)) begin
      if (!enable) $assertoff(0, "tb.dut.u_sha3.FsmKnown_A");
      else         $asserton(0, "tb.dut.u_sha3.FsmKnown_A");
    end else if (!uvm_re_match("*.u_msgfifo.gen_normal_fifo.u_fifo_cnt*", if_proxy.path)) begin
      if (!enable) begin
        $assertoff(0, "tb.dut.u_msgfifo.u_msgfifo.DataKnown_A");
        $assertoff(0, "tb.dut.u_msgfifo.u_msgfifo.gen_normal_fifo.depthShallNotExceedParamDepth");
      end else begin
        $asserton(0, "tb.dut.u_msgfifo.u_msgfifo.DataKnown_A");
        $asserton(0, "tb.dut.u_msgfifo.u_msgfifo.gen_normal_fifo.depthShallNotExceedParamDepth");
      end
    end
  endfunction: sec_cm_fi_ctrl_svas

endclass
