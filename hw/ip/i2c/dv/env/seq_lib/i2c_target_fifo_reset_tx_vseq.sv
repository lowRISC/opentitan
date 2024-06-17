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

    cfg.read_rnd_data = 1;
    cfg.rd_pct = 3;
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
    `uvm_info(`gfn, $sformatf("Flushing txfifo now."), UVM_MEDIUM)
    // flush txfifo
    ral.fifo_ctrl.txrst.set(1'b1);
    csr_update(ral.fifo_ctrl);

    #10us;

    // Flush any leftover data from the fifos
    ral.fifo_ctrl.acqrst.set(1'b1);
    ral.fifo_ctrl.txrst.set(1'b1);
    csr_update(ral.fifo_ctrl);
    `uvm_info(`gfn, $sformatf("Resetting scoreboard now."), UVM_MEDIUM)
    // clean up sb
    cfg.scoreboard.reset();

    // random delay before the next round
    #($urandom_range(1, 5) * 10us);
  endtask

  task proc_intr_cmdcomplete();
    // read acq fifo in 'body' task
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

endclass: i2c_target_fifo_reset_tx_vseq
