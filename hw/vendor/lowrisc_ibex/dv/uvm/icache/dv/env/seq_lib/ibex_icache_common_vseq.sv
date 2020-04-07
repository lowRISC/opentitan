// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_common_vseq extends ibex_icache_base_vseq;
  `uvm_object_utils(ibex_icache_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    // TODO: implement the body of the common virtual sequence
  endtask : body


endclass
