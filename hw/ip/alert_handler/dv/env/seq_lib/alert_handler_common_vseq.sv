// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_common_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_common_vseq)

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
      // these should not be written since they have sideffects on write access
      // of the other regs
      csr_excl.add_excl({scope, ".", "regen"},        CsrExclWrite);
      csr_excl.add_excl({scope, ".", "classa_clren"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "classb_clren"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "classc_clren"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "classd_clren"}, CsrExclWrite);
      // these regs are write only
      csr_excl.add_excl({scope, ".", "classa_clr"},   CsrExclWriteCheck);
      csr_excl.add_excl({scope, ".", "classb_clr"},   CsrExclWriteCheck);
      csr_excl.add_excl({scope, ".", "classc_clr"},   CsrExclWriteCheck);
      csr_excl.add_excl({scope, ".", "classd_clr"},   CsrExclWriteCheck);
      // exclude due to side effects on intr state reg
      csr_excl.add_excl({scope, ".", "intr_test"},    CsrExclWrite);
    end
  endfunction

endclass
