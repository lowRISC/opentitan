// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_common_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_entropy_src_init = 1'b0;

    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // The random reset wrapper applies the resets, so the child it runs must not apply any.
  //
  // This extends a function from cip_base_vseq
  protected function void configure_child_vseq(uvm_sequence child_vseq);
    entropy_src_base_vseq entropy_src_child_vseq;

    super.configure_child_vseq(child_vseq);
    `downcast(entropy_src_child_vseq, child_vseq)
    entropy_src_child_vseq.external_reset = 1'b1;
  endfunction : configure_child_vseq

endclass
