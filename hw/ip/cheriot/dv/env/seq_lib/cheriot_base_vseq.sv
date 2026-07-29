// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cheriot_base_vseq extends cip_base_vseq #(
    .RAL_T               (cheriot_regs_reg_block),
    .CFG_T               (cheriot_env_cfg),
    .COV_T               (cheriot_env_cov),
    .VIRTUAL_SEQUENCER_T (cheriot_virtual_sequencer)
  );
  `uvm_object_utils(cheriot_base_vseq)

  // various knobs to enable certain routines
  bit do_cheriot_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_cheriot_init) cheriot_init();
  endtask

  virtual task dut_shutdown();
    // check for pending cheriot operations and wait for them to complete
    // TODO
  endtask

  // setup basic cheriot features
  virtual task cheriot_init();
  endtask

endclass : cheriot_base_vseq
