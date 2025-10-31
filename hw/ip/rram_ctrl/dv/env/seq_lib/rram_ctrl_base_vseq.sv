// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rram_ctrl_reg_block),
    .CFG_T               (rram_ctrl_env_cfg),
    .COV_T               (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rram_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_rram_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_rram_ctrl_init) rram_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending rram_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic rram_ctrl features
  virtual task rram_ctrl_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : rram_ctrl_base_vseq
