// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_caching_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_caching_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    // Constrain branch targets and force the cache to be enabled
    core_seq.constrain_branches = 1'b1;
    core_seq.initial_enable     = 1'b1;
    core_seq.const_enable       = 1'b1;

    // Try not to invalidate the cache (since that will lower the hit rate)
    core_seq.avoid_invalidation = 1'b1;

  endtask : pre_start

endclass : ibex_icache_caching_vseq
