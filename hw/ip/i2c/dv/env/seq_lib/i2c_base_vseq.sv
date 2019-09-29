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

  // enable interrupts
  rand bit [NumI2cIntr-1:0] en_intr;

  // random delays to access fifo/intr, may be controlled in extended seq
  rand uint dly_to_access_fifo;

  // various knobs to enable certain routines
  bit do_interrupt      = 1'b1;

  constraint dly_to_access_fifo_c {
    dly_to_access_fifo inside {[1:100]};
  }

  `uvm_object_new

  virtual task body();
    // override cip_base_vseq.body()
  endtask : body

  virtual task dut_shutdown();
    // check for pending i2c operations and wait for them to complete
    super.dut_shutdown();
    // wait for tx and rx operations to complete
    `uvm_info(`gfn, "waiting for idle", UVM_HIGH)
    cfg.m_i2c_agent_cfg.vif.wait_for_idle();
    `uvm_info(`gfn, "done waiting for idle", UVM_HIGH)
  endtask

  // setup basic i2c features
  virtual task i2c_init();
    //`uvm_info(`gfn, "Initialize I2C registers")
  endtask

endclass : i2c_base_vseq
