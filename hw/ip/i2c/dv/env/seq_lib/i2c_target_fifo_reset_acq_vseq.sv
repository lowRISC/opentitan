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

    cfg.read_rnd_data = 1;
    seq_runtime_us = 10000;
  endtask

  virtual task body();
    #50us;
    fork
      super.body();
      process_acq();
    join
  endtask: body

  virtual task end_of_stim_hook();
    // flush acq
    ral.fifo_ctrl.acqrst.set(1'b1);
    csr_update(ral.fifo_ctrl);

    // clean up sb
    cfg.scb_h.target_mode_wr_exp_fifo.flush();
    cfg.scb_h.target_mode_wr_obs_fifo.flush();
    cfg.scb_h.skip_acq_comp = 1;

    #10us;
    tran_id = 0;
    cfg.scb_h.obs_wr_id = 0;
    cfg.scb_h.skip_acq_comp = 0;

    // random delay before the next round
    #($urandom_range(1, 5) * 10us);
  endtask

  task proc_intr_cmdcomplete();
    // read acq fifo in 'body' task
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

endclass: i2c_target_fifo_reset_acq_vseq
