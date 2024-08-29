// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_common_vseq extends keymgr_dpe_base_vseq;
  `uvm_object_utils(keymgr_dpe_common_vseq)

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
    do_keymgr_dpe_init = 1'b0;
    // randomly changing edn interval value makes EDN req unpredictable,
    // disable the EDN SVA in the keymgr_if.
    cfg.keymgr_dpe_vif.en_chk = 0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task read_and_check_all_csrs_after_reset();
    // need to set keymgr_en to be On, before it can be read back with correct init values
    cfg.keymgr_dpe_vif.init(do_rand_otp_key, do_invalid_otp_key);
    delay_after_reset_before_access_csr();

    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");
    csr_vseq_done = 0;
    // in these 2 test, we have a separate thread to invoke csr_rw
    // but `working_state` needs couple cylces to be updated after fault injection, it's hard to
    // predict its value cycle accurately. Exclude it and read it out after FI for check.
    if (common_seq_type inside {"shadow_reg_errors_with_csr_rw", "tl_intg_err"}) begin
      ral.get_excl_item().add_excl(ral.working_state.`gfn, CsrExclWriteCheck, CsrRwTest);
    end
    super.run_csr_vseq(csr_test_type, num_test_csrs, do_rand_wr_and_reset, models, ral_name);
    csr_vseq_done = 1;
  endtask

  virtual task check_tl_intg_error_response();
    super.check_tl_intg_error_response();
    // wait until csr_rw seq is done, as below operation may affect csr_rw to predict CSR values
    wait (csr_vseq_done);
    check_after_fi();
  endtask

  virtual task read_check_shadow_reg_status(string msg_id);
    super.read_check_shadow_reg_status(msg_id);

    // Don't do additional operation in shadow_reg_errors_with_csr_rw, as the csr_rw_seq runs in
    // parallel and issueing an operation affects CSR access.
    // If control_shadowed has a storage error, this reg is locked. We can't update its value to do
    // an advance operation.
    if (`gmv(ral.fault_status.shadow) && common_seq_type != "shadow_reg_errors_with_csr_rw" &&
      !ral.control_shadowed.get_shadow_storage_err()) begin
      // wait until csr_rw seq is done, as below operation may affect csr_rw to predict CSR values
      wait (csr_vseq_done);
      check_after_fi();
    end
  endtask

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit[TL_DW-1:0] exp;

    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (!uvm_re_match("*.u_reseed_ctrl*", if_proxy.path)) begin
          exp[keymgr_pkg::FaultReseedCnt] = 1;
          if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultReseedCnt);
        end else if (!uvm_re_match("*.u_kmac_if*", if_proxy.path)) begin
          exp[keymgr_pkg::FaultKmacFsm] = 1;
          if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultKmacFsm);
        end else begin
          exp[keymgr_pkg::FaultCtrlCnt] = 1;
          if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultCtrlCnt);
        end
      end
      SecCmPrimSparseFsmFlop: begin
        if (!uvm_re_match("*.u_kmac_if*", if_proxy.path)) begin
          exp[keymgr_pkg::FaultKmacFsm] = 1;
          if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultKmacFsm);
        end else if (!uvm_re_match("*.u_sideload_ctrl*", if_proxy.path)) begin
          exp[keymgr_pkg::FaultSideFsm] = 1;
          if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultSideFsm);
        end else begin
          exp[keymgr_pkg::FaultCtrlFsm] = 1;
          if (cfg.en_cov) cov.fault_status_cg.sample(keymgr_pkg::FaultCtrlFsm);
        end
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
    csr_rd_check(.ptr(ral.fault_status), .compare_value(exp));

    check_after_fi();
  endtask : check_sec_cm_fi_resp

   virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
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
      SecCmPrimSparseFsmFlop: begin
        if (enable) begin
          $asserton(0, "tb.dut.u_ctrl.LoadKey_A");
          $asserton(0, "tb.dut.u_sideload_ctrl.KmacKeySource_a");
          $asserton(0, "tb.dut.u_ctrl.DataEn_A");
          $asserton(0, "tb.dut.u_ctrl.DataEnDis_A");
        end else begin
          $assertoff(0, "tb.dut.u_ctrl.LoadKey_A");
          $assertoff(0, "tb.dut.u_sideload_ctrl.KmacKeySource_a");
          $assertoff(0, "tb.dut.u_ctrl.DataEn_A");
          $assertoff(0, "tb.dut.u_ctrl.DataEnDis_A");
        end
      end
      SecCmPrimOnehot: begin
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
