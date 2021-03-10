// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dcd_base_vseq extends cip_base_vseq #(
    .RAL_T               (dcd_reg_block),
    .CFG_T               (dcd_env_cfg),
    .COV_T               (dcd_env_cov),
    .VIRTUAL_SEQUENCER_T (dcd_virtual_sequencer)
  );
  `uvm_object_utils(dcd_base_vseq)

  // various knobs to enable certain routines
  bit do_dcd_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_dcd_init) dcd_init();
  endtask

  virtual task dut_shutdown();
    // check for pending dcd operations and wait for them to complete
    // TODO
  endtask

  // setup basic dcd features
  virtual task dcd_init();
    `uvm_info(`gfn, "Initializating dcd, nothing to do at the moment", UVM_MEDIUM)
  endtask // dcd_init

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      cfg.clk_aon_rst_vif.apply_reset();
    end
    super.apply_reset(kind);
  endtask // apply_reset

endclass : dcd_base_vseq
