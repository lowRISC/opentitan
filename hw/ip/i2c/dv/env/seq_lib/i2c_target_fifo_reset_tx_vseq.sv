// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence asserts 'fifo_ctrl.txrst' at the end of transaction.
// Upon receiving txrst, dut and tb wil flush tx_fifo and expect
// to receive a new tx data. acq process shouldn't be affected by setting txrst.
class i2c_target_fifo_reset_tx_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_fifo_reset_tx_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    cfg.scb_h.read_rnd_data = 1;
    cfg.rd_pct = 3;
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
    ral.fifo_ctrl.txrst.set(1'b1);
    csr_update(ral.fifo_ctrl);

    // clean up sb
    cfg.scb_h.target_mode_rd_obs_fifo.flush();
    cfg.scb_h.mirrored_txdata = '{};

    // random delay before the next round
    #($urandom_range(1, 5) * 10us);
  endtask

  task proc_intr_cmdcomplete();
    // read acq fifo in 'body' task
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

endclass: i2c_target_fifo_reset_tx_vseq
