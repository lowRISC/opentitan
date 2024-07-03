// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence asserts 'fifo_ctrl.acqrst' at the end of transaction.
// Upon asserting 'fifo_ctrl.acqrst', dut has to be 'target idle' state.
// Before it resume a new transaction, all tb pipeline are flushed.
class i2c_target_fifo_reset_acq_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_fifo_reset_acq_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    seq_runtime_us = 10000;

    // Use a basic Agent sequence that drives all items it is passed.
    i2c_base_seq::type_id::set_type_override(i2c_target_base_seq::get_type());
  endtask

  virtual task body();
    #50us;
    fork
      super.body();
      process_acq();
    join
  endtask: body

  virtual task end_of_stim_hook();
    // Flush acqfifo
    ral.fifo_ctrl.acqrst.set(1'b1);
    csr_update(ral.fifo_ctrl);

    #10us;

    `uvm_info(`gfn, $sformatf("Resetting scoreboard now."), UVM_MEDIUM)
    // Clear base-vseq id for exp_items
    stim_id = 0;
    // Flush any leftover data from the fifos
    ral.fifo_ctrl.acqrst.set(1'b1);
    ral.fifo_ctrl.txrst.set(1'b1);
    csr_update(ral.fifo_ctrl);
    // Clean up sb
    cfg.scoreboard.reset();

    // random delay before the next round
    #($urandom_range(1, 5) * 10us);
  endtask

  task proc_intr_cmdcomplete();
    // read acq fifo in 'body' task
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

endclass: i2c_target_fifo_reset_acq_vseq
