// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_base_vseq extends dv_base_vseq #(
    .CFG_T               (otbn_env_cfg),
    .COV_T               (otbn_env_cov),
    .VIRTUAL_SEQUENCER_T (otbn_virtual_sequencer)
  );
  `uvm_object_utils(otbn_base_vseq)

  // various knobs to enable certain routines
  bit do_otbn_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_otbn_init) otbn_init();
  endtask

  virtual task dut_shutdown();
    // check for pending otbn operations and wait for them to complete
    // TODO
  endtask

  // setup basic otbn features
  virtual task otbn_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : otbn_base_vseq
