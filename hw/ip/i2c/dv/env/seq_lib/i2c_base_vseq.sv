// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_base_vseq extends cip_base_vseq #(
    .CFG_T               (i2c_env_cfg),
    .RAL_T               (i2c_reg_block),
    .COV_T               (i2c_env_cov),
    .VIRTUAL_SEQUENCER_T (i2c_virtual_sequencer)
  );
  `uvm_object_utils(i2c_base_vseq)

  // various knobs to enable certain routines
  bit do_i2c_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_i2c_init) i2c_init();
  endtask

  virtual task dut_shutdown();
    // check for pending i2c operations and wait for them to complete
    // TODO
  endtask

  // setup basic i2c features
  virtual task i2c_init();
    //`uvm_info(`gfn, "Initialize I2C registers")
  endtask

endclass : i2c_base_vseq
