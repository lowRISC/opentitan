// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test provides a basic check of the TXFIFO watermarks and watermark
// interrupts.
//
// Desc:
//   Stimulate read transactions, filling the TXFIFO with data before starting
//   driving the bus. By choosing a read-size which is larger than the
//   configured tx_threshold watermark, we can see the "tx_threshold" interrupt
//   begin asserted when populating with data, de-assert once the TXFIFO is filled
//   beyond the threshold, then assert again as the bus stimulus empties the fifo.
//
// (DUT:Agent == Target:Controller)
// This test is interrupt driven, so needs the plusarg '+use_intr_handler=1' set.
//
class i2c_target_fifo_watermarks_tx_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_fifo_watermarks_tx_vseq)
  `uvm_object_new

  // EXP
  uint tx_threshold_exp_state;
  uint tx_threshold_exp_intr_poscnt = 0;
  uint tx_threshold_exp_intr_negcnt = 0;

  // OBS
  uint tx_threshold_obs_intr_poscnt = 0;
  uint tx_threshold_obs_intr_negcnt = 0;

  virtual task pre_start();
    super.pre_start();

    seq_runtime_us = 1_000;

    // Only read transactions.
    cfg.wr_pct = 0;

    // Constrain each transaction to be larger than the configured 'tx_thresh'.
    cfg.min_data = tx_thresh + 1;
    cfg.max_data = I2C_TX_FIFO_DEPTH;

    // Disable ACK-Control mode ('acqstretch' can only be due to acqfull)
    cfg.ack_ctrl_en = 0;

    // Use a basic Agent sequence that drives all items it is passed.
    i2c_base_seq::type_id::set_type_override(i2c_target_base_seq::get_type());
  endtask: pre_start

  virtual task body();
    fork
      super.body();
      count_edge_intr(TxThreshold, tx_threshold_obs_intr_poscnt, tx_threshold_obs_intr_negcnt);
    join_any
  endtask: body

  // This hook is called at the start of each new stimulus iteration.
  //
  virtual task setup_hook();
    // Cleanup for next iteration.
    tx_threshold_obs_intr_poscnt = 0;
    tx_threshold_obs_intr_negcnt = 0;
    tx_threshold_exp_intr_poscnt = 0;
    tx_threshold_exp_intr_negcnt = 0;
  endtask

  virtual task start_of_stim_hook();
    // At the start of stimulus, the txfifo should be empty.
    csr_rd_check(.ptr(ral.target_fifo_status.txlvl), .compare_value(0));
    // Unless the threshold is also configured to zero, this means the
    // interrupt should be asserted.
    tx_threshold_exp_state = bit'(tx_thresh > 0);
    check_one_intr(TxThreshold, tx_threshold_exp_state);

    // Write all rdata for the next read transaction to the TXFIFO
    while (read_rcvd_q.size() > 0) write_tx_fifo();

    // This should be enough data to now exceed the watermark, and hence the
    // interrupt will deassert (if the interrupt was active to begin with).
    // This check is done before any agent-stimulus is generated, so data
    // cannot yet leave the txfifo.
    if (tx_threshold_exp_state) tx_threshold_exp_intr_negcnt++;
    tx_threshold_exp_state = 1'b0;

    `DV_CHECK_EQ(tx_threshold_obs_intr_poscnt, tx_threshold_exp_intr_poscnt,
                 "tx_threshold interrupt did not trigger correctly!")
    `DV_CHECK_EQ(tx_threshold_obs_intr_negcnt, tx_threshold_exp_intr_negcnt,
                 "tx_threshold de-asserted when not expected!")
  endtask

  virtual task end_of_stim_hook();
    bit acq_fifo_empty;

    // After the transaction completes, the txfifo should now be empty, and
    // (unless threshold == 0) the watermark interrupt should be asserted again.
    tx_threshold_exp_state = bit'(tx_thresh > 0);
    if (tx_threshold_exp_state) tx_threshold_exp_intr_poscnt++;

    check_one_intr(TxThreshold, tx_threshold_exp_state);
    `DV_CHECK_EQ(tx_threshold_obs_intr_poscnt, tx_threshold_exp_intr_poscnt,
                 "acq_threshold interrupt did not trigger correctly!")
    `DV_CHECK_EQ(tx_threshold_obs_intr_negcnt, tx_threshold_exp_intr_negcnt,
                 "acq_threshold de-asserted when not expected!")

    // Empty out the ACQFIFO now.
    `uvm_info(`gfn, "Emptying ACQFIFO now.", UVM_MEDIUM)
    read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));
    `uvm_info(`gfn, "ACQFIFO is now empty.", UVM_MEDIUM)

    #1ns; // Otherwise our cleanup races with the scoreboard checking the acqfifo read above.
  endtask

  // Interrupt handler for the "cmd_complete" interrupt
  // (This overrides the parent class impl.)
  virtual task proc_intr_cmdcomplete();
    `uvm_info(`gfn, "proc_intr_cmdcomplete()", UVM_MEDIUM)
    // Simply acknowledge and clear this 'event'-type interrupt.
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

  // Interrupt handler for a '"tx_stretch" interrupt.
  //
  // Desc:
  //   In this test, we add all the rddata into the TXFIFO before the
  //   agent begins the read transaction. However, the DUT will still
  //   stretch (tx_stretch) once more than one item is in the ACQFIFO.
  //   This handler simply reads the ACQFIFO once when called.
  virtual task proc_intr_txstretch();
    bit acq_fifo_empty;
    `uvm_info(`gfn, "proc_intr_acqstretch()", UVM_MEDIUM)
    `uvm_info(`gfn, "Reading ACQFIFO once now.", UVM_MEDIUM)
    read_acq_fifo(.read_one(1), .acq_fifo_empty(acq_fifo_empty));
    `uvm_info(`gfn, "ACQFIFO read once.", UVM_MEDIUM)
  endtask: proc_intr_txstretch

endclass: i2c_target_fifo_watermarks_tx_vseq
