// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_base_vseq extends dv_base_vseq #(
    .CFG_T               (pattgen_env_cfg),
    .COV_T               (pattgen_env_cov),
    .VIRTUAL_SEQUENCER_T (pattgen_virtual_sequencer)
  );
  `uvm_object_utils(pattgen_base_vseq)

  // various knobs to enable certain routines
  bit do_pattgen_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_pattgen_init) pattgen_init();
  endtask

  virtual task dut_shutdown();
    // check for pending pattgen operations and wait for them to complete
    // TODO
  endtask

  // setup basic pattgen features
  virtual task pattgen_init();
    // TODO
  endtask

endclass : pattgen_base_vseq
