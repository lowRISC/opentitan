// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that injects ECC errors and checks we deal with them correctly.
//
// This is based on the caching vseq, which means we should see lots of cache hits (some of which
// will be corrupt).

class ibex_icache_ecc_vseq extends ibex_icache_caching_vseq;

  `uvm_object_utils(ibex_icache_ecc_vseq)
  `uvm_object_new

  virtual task pre_start();
    enable_ecc_errors = 1'b1;
    super.pre_start();
  endtask : pre_start

  // Wrap the underlying body, setting the disable_caching_ratio_test flag to tell the scoreboard
  // not to track cache hit ratios. This test corrupts data in the ICache's memory. The corruptions
  // are spotted, and behave as if the cache missed. This (obviously) lowers the cache hit rate, so
  // we don't want the test to make sure it's high enough.
  virtual task body();
    bit old_dcrt = p_sequencer.cfg.disable_caching_ratio_test;
    p_sequencer.cfg.disable_caching_ratio_test = 1'b1;

    super.body();

    p_sequencer.cfg.disable_caching_ratio_test = old_dcrt;
  endtask : body

endclass : ibex_icache_ecc_vseq
