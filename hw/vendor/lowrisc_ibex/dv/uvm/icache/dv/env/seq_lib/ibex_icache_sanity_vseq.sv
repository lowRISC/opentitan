// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic sanity test

class ibex_icache_sanity_vseq extends ibex_icache_base_vseq;
  `uvm_object_utils(ibex_icache_sanity_vseq)

  `uvm_object_new

  // A sanity sequence for the core agent
  ibex_icache_core_sanity_seq core_seq;

  task body();
    // TODO: This currently just drives the core sequence (which clearly isn't going to work!)
    `uvm_create_on(core_seq, p_sequencer.core_sequencer_h)
    `DV_CHECK_RANDOMIZE_FATAL(core_seq)
    core_seq.start(p_sequencer.core_sequencer_h);
  endtask : body

endclass : ibex_icache_sanity_vseq
