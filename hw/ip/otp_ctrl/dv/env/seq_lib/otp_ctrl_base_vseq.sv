// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (otp_ctrl_reg_block),
    .CFG_T               (otp_ctrl_env_cfg),
    .COV_T               (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (otp_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(otp_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_otp_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_otp_ctrl_init) otp_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending otp_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic otp_ctrl features
  virtual task otp_ctrl_init();
    cfg.pwr_otp_vif.drive_pin(0, 0);
    // reset memory to avoid readout X
    cfg.mem_bkdr_vif.clear_mem();
  endtask

endclass : otp_ctrl_base_vseq
