// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_base_vseq extends dv_base_vseq #(
    .CFG_T               (ibex_icache_env_cfg),
    .COV_T               (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T (ibex_icache_virtual_sequencer)
  );
  `uvm_object_utils(ibex_icache_base_vseq)

  // various knobs to enable certain routines
  bit do_ibex_icache_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_ibex_icache_init) ibex_icache_init();
  endtask

  virtual task dut_shutdown();
    // check for pending ibex_icache operations and wait for them to complete
    // TODO
  endtask

  // setup basic ibex_icache features
  virtual task ibex_icache_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : ibex_icache_base_vseq
