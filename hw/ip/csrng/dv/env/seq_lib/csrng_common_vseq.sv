// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_common_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_csrng_init = 1'b0;

    super.pre_start();
  endtask

  virtual task body();
    // When run from a stress test, a command blocked on entropy may have set the cs_entropy_req
    // interrupt, which the common interrupt test doesn't expect.
    if (`gmv(ral.ctrl.enable) == MuBi4True) clear_all_interrupts();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
