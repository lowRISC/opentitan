// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_base_vseq extends cip_base_vseq #(
    .RAL_T               (aon_timer_reg_block),
    .CFG_T               (aon_timer_env_cfg),
    .COV_T               (aon_timer_env_cov),
    .VIRTUAL_SEQUENCER_T (aon_timer_virtual_sequencer)
  );
  `uvm_object_utils(aon_timer_base_vseq)

  // various knobs to enable certain routines
  bit do_aon_timer_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_aon_timer_init) aon_timer_init();
  endtask

  virtual task dut_shutdown();
    // check for pending aon_timer operations and wait for them to complete
    // TODO
  endtask

  // setup basic aon_timer features
  virtual task aon_timer_init();
    `uvm_info(`gfn, "Initializating aon timer, nothing to do at the moment", UVM_MEDIUM)
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      cfg.clk_aon_rst_vif.apply_reset();
    end
    super.apply_reset(kind);
  endtask // apply_reset

endclass : aon_timer_base_vseq
