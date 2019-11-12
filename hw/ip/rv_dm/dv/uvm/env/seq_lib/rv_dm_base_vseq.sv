// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_base_vseq extends dv_base_vseq #(
    .CFG_T               (rv_dm_env_cfg),
    .RAL_T               (rv_dm_reg_block),
    .COV_T               (rv_dm_env_cov),
    .VIRTUAL_SEQUENCER_T (rv_dm_virtual_sequencer)
  );
  `uvm_object_utils(rv_dm_base_vseq)

  // various knobs to enable certain routines
  bit do_rv_dm_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // set inputs to 0
    cfg.rv_dm_vif.testmode = '0;
    cfg.rv_dm_vif.unavailable = '{default:0};

    super.dut_init();
    if (do_rv_dm_init) rv_dm_init();
  endtask

  virtual task dut_shutdown();
    // check for pending rv_dm operations and wait for them to complete
    // TODO
  endtask

  // setup basic rv_dm features
  virtual task rv_dm_init();
  endtask

endclass : rv_dm_base_vseq
