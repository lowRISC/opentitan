// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_common_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_keymgr_init = 1'b0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task read_and_check_all_csrs_after_reset();
    delay_after_reset_before_access_csr();

    super.read_and_check_all_csrs_after_reset();
  endtask

endclass
