// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_common_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_common_vseq)

  // Set this flag low before calling csr seq, then set it back to 1 when it's done
  // If no csr seq is called, this flag should be high
  bit csr_vseq_done = 1;

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  // override this delay for keymgr_stress_all_with_rand_reset, as most of vseq finishes less than
  // 10k cycles
  constraint rand_reset_delay_c {
    rand_reset_delay dist {
        [1     : 100]     :/ 1,
        [101   : 2_000]   :/ 6,
        [2_001 : 10_000]  :/ 1
    };
  }

  virtual task pre_start();
    do_keymgr_init = 1'b0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task read_and_check_all_csrs_after_reset();
    // need to set keymgr_en to be On, before it can be read back with correct init values
    cfg.keymgr_vif.init();
    delay_after_reset_before_access_csr();

    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");
    csr_vseq_done = 0;
    super.run_csr_vseq(csr_test_type, num_test_csrs, do_rand_wr_and_reset, models, ral_name);
    csr_vseq_done = 1;
  endtask

  virtual task check_tl_intg_error_response();
    super.check_tl_intg_error_response();
    check_state_after_non_operation_fault();
  endtask

  virtual task read_check_shadow_reg_status(string msg_id);
    super.read_check_shadow_reg_status(msg_id);

    // Don't do additional operation in shadow_reg_errors_with_csr_rw, as the csr_rw_seq runs in
    // parallel and issueing an operation affects CSR access.
    // If control_shadowed has a storage error, this reg is locked. We can't update its value to do
    // an advance operation.
    if (`gmv(ral.fault_status.shadow) && common_seq_type != "shadow_reg_errors_with_csr_rw" &&
      !ral.control_shadowed.get_shadow_storage_err()) begin
      check_state_after_non_operation_fault();
    end
  endtask

  // Check state is StInvalid when there is an non-operation fault like integrity error, storage
  // error.
  virtual task check_state_after_non_operation_fault();
    // wait until csr_rw seq is done, as below operation may affect csr_rw to predict CSR values
    wait(csr_vseq_done);

    // issue an advance operation and check that state enters StInvalid
    keymgr_advance(.wait_done(0));
    // waiting for done is called separately as this one expects to be failed
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneFail),
                 .spinwait_delay_ns($urandom_range(0, 100)));
    read_current_state();
    `DV_CHECK_EQ(current_state, keymgr_pkg::StInvalid)
  endtask

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit[TL_DW-1:0] exp;

    // TODO, remove this after #8464 is solved
    if (!uvm_re_match("*.u_kmac_if*", if_proxy.path)) return;

    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (!uvm_re_match("*.u_reseed_ctrl*", if_proxy.path)) begin
          exp[keymgr_pkg::FaultReseedCnt] = 1;
        end else begin
          exp[keymgr_pkg::FaultCtrlCnt] = 1;
        end
      end
      SecCmPrimSparseFsmFlop: begin
        exp[keymgr_pkg::FaultCtrlFsm] = 1;
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
    csr_rd_check(.ptr(ral.fault_status), .compare_value(exp));

    // after an advance, keymgr should enter StInvalid
    keymgr_advance();
    csr_rd_check(.ptr(ral.op_status), .compare_value(keymgr_pkg::OpDoneFail));
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_pkg::StInvalid));
  endtask : check_sec_cm_fi_resp

   virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    // TODO, remove this after #8464 is solved
    // $assertoff(0, "tb.dut.u_kmac_if.u_cnt.u_prim_count_if.ErrorTriggerAlert");

    // TODO, review if we need to disable all these for prim_count
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (enable) begin
          $asserton(0, "tb.keymgr_kmac_intf");
          $asserton(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
          $asserton(0, "tb.dut.u_ctrl.DataEn_A");
          $asserton(0, "tb.dut.u_ctrl.DataEnDis_A");
          $asserton(0, "tb.dut.u_ctrl.CntZero_A");
          $asserton(0, "tb.dut.u_kmac_if.LastStrb_A");
          $asserton(0, "tb.dut.KmacDataKnownO_A");
        end else begin
          $assertoff(0, "tb.keymgr_kmac_intf");
          $assertoff(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
          $assertoff(0, "tb.dut.u_ctrl.DataEn_A");
          $assertoff(0, "tb.dut.u_ctrl.DataEnDis_A");
          $assertoff(0, "tb.dut.u_ctrl.CntZero_A");
          $assertoff(0, "tb.dut.u_kmac_if.LastStrb_A");
          $assertoff(0, "tb.dut.KmacDataKnownO_A");
        end
      end
      SecCmPrimSparseFsmFlop, SecCmPrimOnehot: begin
        // No need to disable any assertion
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
  endfunction: sec_cm_fi_ctrl_svas

  // disable checker in seq, only check in this seq
  virtual function bit get_check_en();
    return 0;
  endfunction

endclass
