// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_base_vseq extends cip_base_vseq #(
    .RAL_T               (kmac_reg_block),
    .CFG_T               (kmac_env_cfg),
    .COV_T               (kmac_env_cov),
    .VIRTUAL_SEQUENCER_T (kmac_virtual_sequencer)
  );
  `uvm_object_utils(kmac_base_vseq)

  // various knobs to enable certain routines
  bit do_kmac_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_kmac_init) kmac_init();
  endtask

  virtual task dut_shutdown();
    // check for pending kmac operations and wait for them to complete
    // TODO
  endtask

  // setup basic kmac features
  virtual task kmac_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : kmac_base_vseq
