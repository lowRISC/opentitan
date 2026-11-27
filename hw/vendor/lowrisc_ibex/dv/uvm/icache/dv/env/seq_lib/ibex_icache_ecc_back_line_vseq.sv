// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The back_line sequence with ECC errors. Branching back into a line that is still being fetched
// can put the same line in two ways, so this checks errors on lines held in more than one way.

class ibex_icache_ecc_back_line_vseq extends ibex_icache_back_line_vseq;

  `uvm_object_utils(ibex_icache_ecc_back_line_vseq)
  `uvm_object_new

  // Shared settings that this sequence changes, restored when it ends or is killed
  protected bit          saved = 1'b0;
  protected bit          old_ecc_en, old_dcrt;
  protected int unsigned old_pct;

  virtual task pre_start();
    old_ecc_en = cfg.ram_if.enable_ecc_errors;
    old_pct    = cfg.ram_if.dis_err_pct;
    old_dcrt   = p_sequencer.cfg.disable_caching_ratio_test;
    saved      = 1'b1;

    // Corrupt about one read in ten, so that errors often land on a line held in two ways. Corrupt
    // lines behave as misses, which lowers the hit rate, so don't track it (as in ecc_vseq).
    cfg.ram_if.enable_ecc_errors               = 1'b1;
    cfg.ram_if.dis_err_pct                     = 90;
    p_sequencer.cfg.disable_caching_ratio_test = 1'b1;

    super.pre_start();

    // Invalidate first to encourage a new memory seed. With the initial seed, fetches near address
    // zero get bus errors, so nothing is cached there.
    core_seq.must_invalidate = 1'b1;
  endtask : pre_start

  virtual task post_start();
    restore_settings();
    super.post_start();
  endtask : post_start

  // The combo sequences kill a child on a random reset, which skips post_start.
  virtual function void do_kill();
    restore_settings();
    super.do_kill();
  endfunction : do_kill

  protected function void restore_settings();
    if (!saved) return;
    cfg.ram_if.enable_ecc_errors               = old_ecc_en;
    cfg.ram_if.dis_err_pct                     = old_pct;
    p_sequencer.cfg.disable_caching_ratio_test = old_dcrt;
    saved                                      = 1'b0;
  endfunction : restore_settings

endclass : ibex_icache_ecc_back_line_vseq
