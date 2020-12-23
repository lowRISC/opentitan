// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_common_vseq extends kmac_base_vseq;
  `uvm_object_utils(kmac_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    do_kmac_init = 1'b0;
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
