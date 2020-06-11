// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_many_errors_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_many_errors_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    // Constrain branch targets as with the many_errors test, but allow the cache to be enabled or
    // disabled
    core_seq.constrain_branches = 1'b1;
    core_seq.initial_enable     = 1'b1;

  endtask : pre_start

endclass : ibex_icache_many_errors_vseq
