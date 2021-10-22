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

  virtual task run_csr_vseq(string csr_test_type = "",
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1);
    csr_vseq_done = 0;
    super.run_csr_vseq(csr_test_type, num_test_csrs, do_rand_wr_and_reset);
    csr_vseq_done = 1;
  endtask

  virtual task check_tl_intg_error_response();
    super.check_tl_intg_error_response();
    check_state_after_non_operation_fault();
  endtask

  virtual task read_check_shadow_reg_status(string msg_id);
    super.read_check_shadow_reg_status(msg_id);

    if (`gmv(ral.fault_status.shadow)) begin
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
endclass
