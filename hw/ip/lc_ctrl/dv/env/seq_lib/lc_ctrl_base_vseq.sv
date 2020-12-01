// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (lc_ctrl_reg_block),
    .CFG_T               (lc_ctrl_env_cfg),
    .COV_T               (lc_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (lc_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(lc_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_lc_ctrl_init = 1'b1;
  bit do_lc_pwr_init  = 1'b1;

  `uvm_object_new

  virtual task pre_start();
    // LC_CTRL does not have interrupts
    do_clear_all_interrupts = 0;
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    cfg.lc_ctrl_vif.init();
    if (do_lc_ctrl_init) lc_ctrl_init();
    if (do_lc_pwr_init) lc_pwr_init();
  endtask

  virtual task dut_shutdown();
    // check for pending lc_ctrl operations and wait for them to complete
    // TODO
  endtask

  // drive lc_pwr req pin to initialize LC, and wait until init is done
  virtual task lc_pwr_init();
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 1);
    wait(cfg.pwr_lc_vif.pins[LcPwrDoneRsp] == 1);
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
  endtask

  // setup basic lc_ctrl features
  virtual task lc_ctrl_init();
    //`uvm_error(`gfn, "FIXME")
  endtask

endclass : lc_ctrl_base_vseq
