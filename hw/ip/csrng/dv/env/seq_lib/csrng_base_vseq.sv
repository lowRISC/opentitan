// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_base_vseq extends cip_base_vseq #(
    .RAL_T               (csrng_reg_block),
    .CFG_T               (csrng_env_cfg),
    .COV_T               (csrng_env_cov),
    .VIRTUAL_SEQUENCER_T (csrng_virtual_sequencer)
  );
  `uvm_object_utils(csrng_base_vseq)

  // various knobs to enable certain routines
  bit do_csrng_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_csrng_init) csrng_init();
  endtask

  virtual task dut_shutdown();
    // check for pending csrng operations and wait for them to complete
    // TODO
  endtask

  // setup basic csrng features
  virtual task csrng_init();
  endtask

endclass : csrng_base_vseq
