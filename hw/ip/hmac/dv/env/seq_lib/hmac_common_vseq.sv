// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_common_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task pre_body();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");
    // write exclusions - these should not apply to hw_reset test
    if (csr_test_type != "hw_reset") begin
      // the following csrs is WO - uvm_reg_field assumes reading WO will result in bus error; in
      // reality it does not - dut reads back 0s, but uvm_reg_field expects original written value
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "wipe_secret"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "key?"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "msg_fifo"}, CsrExclWrite);

      // don't enable hmac and sha data paths - we will do that in functional tests
      csr_excl.add_excl({scope, ".", "cfg.hmac_en"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "cfg.sha_en"}, CsrExclWrite);
    end

    // design assertion : after hash_start sets, can only wr msg or set hash_process
    csr_excl.add_excl({scope, ".", "cmd.hash_start"}, CsrExclWrite);
    // design assertion : hash_process can be set only after hash_start is set
    csr_excl.add_excl({scope, ".", "cmd.hash_process"}, CsrExclWrite);
  endfunction

endclass
