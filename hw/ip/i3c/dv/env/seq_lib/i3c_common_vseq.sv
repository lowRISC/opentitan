// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i3c_common_vseq extends i3c_base_vseq;
  `uvm_object_utils(i3c_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    // Walk the DAT and the DCT with masks; see i3c_csr_mem_walk_seq.
    csr_mem_walk_seq::type_id::set_type_override(i3c_csr_mem_walk_seq::get_type());
    super.pre_start();
  endtask : pre_start

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
