// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (sysrst_ctrl_reg_block),
    .CFG_T               (sysrst_ctrl_env_cfg),
    .COV_T               (sysrst_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (sysrst_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(sysrst_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_sysrst_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_sysrst_ctrl_init) sysrst_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending sysrst_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic sysrst_ctrl features
  virtual task sysrst_ctrl_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : sysrst_ctrl_base_vseq
