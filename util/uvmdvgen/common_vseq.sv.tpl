// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${name}_common_vseq extends ${name}_base_vseq;
  `uvm_object_utils(${name}_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
% if is_cip:
    run_common_vseq_wrapper(num_trans);
% elif has_ral:
    run_csr_vseq_wrapper(num_trans);
% endif
  endtask : body

endclass
