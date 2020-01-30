// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_common_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");

    // write exclusions - these should not apply to hw_reset test
    if (csr_test_type != "hw_reset") begin
      csr_excl.add_excl({scope, ".", "trigger"      }, CsrExclWriteCheck);
      csr_excl.add_excl({scope, ".", "ctrl"         }, CsrExclWriteCheck);

      // exclude dataout/status because they change once data in has been written
      csr_excl.add_excl({scope, ".", "status"       }, CsrExclWriteCheck);
      csr_excl.add_excl({scope, ".", "data_out*"    }, CsrExclWriteCheck);
    end

  endfunction
endclass
