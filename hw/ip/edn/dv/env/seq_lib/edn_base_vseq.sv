// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_base_vseq extends cip_base_vseq #(
    .RAL_T               (edn_reg_block),
    .CFG_T               (edn_env_cfg),
    .COV_T               (edn_env_cov),
    .VIRTUAL_SEQUENCER_T (edn_virtual_sequencer)
  );
  `uvm_object_utils(edn_base_vseq)

  // various knobs to enable certain routines
  bit do_edn_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_edn_init) edn_init();
  endtask

  virtual task dut_shutdown();
    // check for pending edn operations and wait for them to complete
    // TODO
  endtask

  // setup basic edn features
  virtual task edn_init();
  endtask

endclass : edn_base_vseq
