// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (racl_ctrl_reg_block),
    .CFG_T               (racl_ctrl_env_cfg),
    .COV_T               (racl_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (racl_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(racl_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_racl_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_racl_ctrl_init) racl_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending racl_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic racl_ctrl features
  virtual task racl_ctrl_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : racl_ctrl_base_vseq
