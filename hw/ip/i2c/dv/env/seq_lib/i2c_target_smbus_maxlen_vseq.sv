// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This directed test aims to check the I2C block can absorb a max-length SMBus message
// without software intervention mid-message (e.g. to drain the ACQFIFO, or handle interrupts).
//
// - Stimulate a max-length transfer (Block-Write of 255 bytes)
// - Disable all interrupt/polling based handlers
// - Wait for the command-complete interrupt to signal the end of the transfer
// - Readback the transfer and check it was received correctly (done via scoreboard)
//
class i2c_target_smbus_maxlen_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_smbus_maxlen_vseq)
  `uvm_object_new

  // The maximum number of data-bytes in a SMBus Block Write
  // 1 - command code
  // 1 - byte count
  // 255 - data
  // 1 - PEC
  int smbus_maxlen = 258;

  virtual task pre_start();
    super.pre_start();

    cfg.min_data = smbus_maxlen;
    cfg.max_data = smbus_maxlen;
    cfg.rs_pct = 0; // Don't generate any RSTARTs, one single transfer per txn
    cfg.rd_pct = 0; // Block-Write
    cfg.min_num_transfers = 1; // Only 1 transfer in the transaction
    cfg.max_num_transfers = 1;

    // Configure the runtime_base_vseq for just a single transfer before ending.
    stim_cnt_limit = 1;

    // Disable the ack_ctrl module, as 'TARGET_ACK_CTRL.n_bytes' resets at the beginning of each
    // new write transaction, so software intervention would, by definition, be required to
    // increment 'n_bytes' at least once during the transfer.
    cfg.ack_ctrl_en = 0;

    // Use a basic Agent sequence that drives all items it is passed.
    i2c_base_seq::type_id::set_type_override(i2c_target_base_seq::get_type());
  endtask

  virtual task initialization();
    super.initialization();
    // The base-class enables all interrupts by default, so override that behaviour here.

    // Mask all target mode interrupts (except CmdComplete). This test is interrupt-driven
    // (the plusarg '+use_intr_handler=1' is set), so this guarantees no interrupt handler will be
    // able to respond to the hardware.
    // If the transfer is able to complete (checked at the scoreboard), we know that the DUT
    // was able to absorb the entire transaction without software intervention.
    ral.intr_enable.acq_threshold.set(1'b0);
    ral.intr_enable.acq_stretch.set(1'b0);
    ral.intr_enable.tx_threshold.set(1'b0);
    ral.intr_enable.tx_stretch.set(1'b0);
    ral.intr_enable.host_timeout.set(1'b0);
    csr_update(ral.intr_enable);
  endtask: initialization

endclass : i2c_target_smbus_maxlen_vseq
