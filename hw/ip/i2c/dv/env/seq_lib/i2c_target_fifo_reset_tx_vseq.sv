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
    seq_runtime = 10000;
  endtask

  task test_event();
    #50us;
    repeat (5) begin
      wait(cfg.m_i2c_agent_cfg.got_stop);
      // stop writing tx fifo and sequence
      pause_seq = 1;

      // flush acq
      ral.fifo_ctrl.txrst.set(1'b1);
      csr_update(ral.fifo_ctrl);

      // clean up sb
      cfg.scb_h.target_mode_rd_obs_fifo.flush();
      cfg.scb_h.mirrored_txdata = '{};

     #10us;
      pause_seq = 0;

      // random delay before the next round
      #($urandom_range(1, 5) * 10us);
    end
  endtask // test_event

  task proc_intr_cmdcomplete();
    // read acq fifo in 'body' task
    clear_interrupt(CmdComplete, 0);
  endtask // proc_itnr_cmd_complete

  task process_acq();
    bit fifo_empty, pop_all;
    int delay;

    while (!cfg.stop_intr_handler) begin
      delay = $urandom_range(0, 10);
      cfg.clk_rst_vif.wait_clks(delay * acq_rd_cyc);
      // pop one all entries by 25% of chance.
      pop_all = ($urandom_range(0,3) > 0);
      read_acq_fifo(~pop_all, fifo_empty);
    end
  endtask // process_acq
endclass // i2c_target_fifo_reset_tx_vseq
