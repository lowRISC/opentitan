// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test provides a basic check of the ACQFIFO watermarks and watermark
// interrupts.
//
// This test stimulates write transfers from the Agent, which fill the acqfifo
// above the configured watermark. After each write transaction, we check that
// the 'AcqThreshold' interrupt has asserted, and remained asserted as a
// status-type irq. After clearing the acqfifo, we then check the interrupt has
// de-asserted.
//
// (DUT:Agent == Target:Controller)
// This test is interrupt driven, so needs the plusarg '+use_intr_handler=1' set.
//
class i2c_target_fifo_watermarks_acq_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_fifo_watermarks_acq_vseq)
  `uvm_object_new

  uint acq_threshold_intr_poscnt;
  uint acq_threshold_intr_negcnt;

  virtual task pre_start();
    super.pre_start();

    seq_runtime_us = 1_000;

    // Only write transactions.
    cfg.rd_pct = 0;

    // Constrain each transaction to be larger than the configured 'acq_thresh'.
    cfg.min_data = acq_thresh;
    cfg.max_data = I2C_ACQ_FIFO_DEPTH;

    // Disable ACK-Control mode ('acqstretch' can only be due to acqfull)
    cfg.ack_ctrl_en = 0;

    // Use a basic Agent sequence that drives all items it is passed.
    i2c_base_seq::type_id::set_type_override(i2c_target_base_seq::get_type());
  endtask: pre_start

  virtual task body();
    fork
      super.body();
      count_edge_intr(AcqThreshold, acq_threshold_intr_poscnt, acq_threshold_intr_negcnt);
    join_any
  endtask: body

  // This hook is called at the start of each new stimulus iteration.
  //
  virtual task setup_hook();
    // Cleanup for next iteration.
    acq_threshold_intr_poscnt = 0;
    acq_threshold_intr_negcnt = 0;
  endtask

  virtual task end_of_stim_hook();
    bit acq_fifo_empty;

    // The ACQFIFO begins empty. We stimulated a transaction which should
    // have generated at-least as much data as the configured threshold.

    check_one_intr(AcqThreshold, 1);
    `DV_CHECK_EQ(acq_threshold_intr_poscnt, 1, "acq_threshold interrupt did not trigger correctly!")
    `DV_CHECK_EQ(acq_threshold_intr_negcnt, 0, "acq_threshold de-asserted when not expected!")

    // If we filled the acqfifo, wait for it to become not full. That way we
    // don't fight the acq_stretch handler. Currently the scoreboard does not
    // tolerate extra reads from the acqfifo.
    csr_spinwait(.ptr(ral.status.acqfull), .exp_data(1'b0));
    // Empty out the ACQFIFO now.
    read_acq_fifo(.read_one(0), .acq_fifo_empty(acq_fifo_empty));

    `DV_CHECK_EQ(acq_threshold_intr_negcnt, 1, "acq_threshold should drop once on fifo drain!")
    check_one_intr(AcqThreshold, 0);
  endtask

  // Interrupt handler for the "cmd_complete" interrupt
  // (This overrides the parent class impl.)
  virtual task proc_intr_cmdcomplete();
    `uvm_info(`gfn, "proc_intr_cmdcomplete()", UVM_MEDIUM)
    // Simply acknowledge and clear this 'event'-type interrupt.
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

  // Interrupt handler for the "acq_stretch" interrupt
  //
  // Desc:
  //   Read the ACQFIFO a single time, which in this test is due to
  //   it becoming full from write txn stimulus.
  //   This is required to allow the stimulus transaction to complete,
  //   if it should be larger than the ACQFIFO, as otherwise we would
  //   stretch indefinitely.
  //
  virtual task proc_intr_acqstretch();
    bit acq_fifo_empty;
    `uvm_info(`gfn, "proc_intr_acqstretch()", UVM_MEDIUM)
    read_acq_fifo(.read_one(1), .acq_fifo_empty(acq_fifo_empty));
  endtask: proc_intr_acqstretch

endclass: i2c_target_fifo_watermarks_acq_vseq
