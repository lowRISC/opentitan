// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A version of the combination vseq that injects resets at unexpected times.

class ibex_icache_reset_vseq extends ibex_icache_combo_vseq;

  `uvm_object_utils(ibex_icache_reset_vseq)
  `uvm_object_new

  task pre_do (bit is_item);
    super.pre_do(is_item);

    // Enable "random reset" functionality, which resets the DUT (and starts a new sequence) at
    // random times.
    random_reset = 1'b1;
  endtask : pre_do

endclass : ibex_icache_reset_vseq
