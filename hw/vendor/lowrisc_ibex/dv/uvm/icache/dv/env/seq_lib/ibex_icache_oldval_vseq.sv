// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_oldval_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_oldval_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    // Constrain branch targets
    core_seq.constrain_branches = 1'b1;

    // Increase the frequency of cache enable/disable toggling
    core_seq.gap_between_toggle_enable = 2;

    // Avoid invalidating the cache (we want old values!)
    core_seq.avoid_invalidation = 1'b1;

  endtask : pre_start

endclass : ibex_icache_oldval_vseq
