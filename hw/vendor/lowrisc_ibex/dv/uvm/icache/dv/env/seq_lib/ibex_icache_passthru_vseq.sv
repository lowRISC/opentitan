// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_passthru_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_passthru_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    // Constrain branch targets and leave the cache disabled.
    core_seq.constrain_branches = 1'b1;
    core_seq.force_disable      = 1'b1;

    // Increase the frequency of seed updates
    mem_seq.gap_between_seeds = 49;

  endtask : pre_start

endclass : ibex_icache_passthru_vseq
