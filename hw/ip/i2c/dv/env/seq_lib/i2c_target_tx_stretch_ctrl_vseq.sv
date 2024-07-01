// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test checks the TX_STRETCH_CTRL feature. (CSR.CTRL.TX_STRETCH_CTRL_EN)
//
// This test stimulates read transfers from the Agent after filling the TXFIFO
// with data. It then awaits the tx_strech interrupt to be asserted, and checks
// that 'TARGET_EVENTS.TX_PENDING' is set. It then clears the pending state to
// allow the transfer to complete, and upon completion checks the pending
// interrupt has not been asserted again.
// We also check that once TX_PENDING is set, SCL remains low until the bit is
// cleared.
//
//
// I2C bus devices configured as: (DUT/Agent == Target/Controller)
// This testcase is interrupt driven, so the plusarg +use_intr_handler=1 is needed.
//
class i2c_target_tx_stretch_ctrl_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_tx_stretch_ctrl_vseq)
  `uvm_object_new

  uint tx_stretch_intr_poscnt;
  uint tx_stretch_intr_negcnt;

  uint transfer_cnt = 0;

  // Constrain the acqfifo watermark threshold to zero, so we can use the
  // interrupt handler for this irq to prevent stretching due to the acqfifo
  // level exceeding 1 for reads.
  constraint acq_thresh_c {acq_thresh == 0;};

  virtual task pre_start();
    super.pre_start();

    seq_runtime_us = 1_000;

    // Only read transactions.
    cfg.wr_pct = 0;

    // Constrain the stimulus generation to disallow transfers without any data.
    // i.e. transfers where the DUT NACKs the address byte.
    // TX_PENDING will not be set in this case, and the interrupt-based checking
    // done below will fail in this case.
    cfg.min_xfer_len = 3;

    // Disable ACK-Control mode
    cfg.ack_ctrl_en = 0;

    // Use a basic Agent sequence that drives all items it is passed.
    i2c_base_seq::type_id::set_type_override(i2c_target_base_seq::get_type());
  endtask: pre_start

  // Augment the base-class initialization to enable our feature under test.
  virtual task initialization();
    super.initialization();

    // Enable the feature we're testing here.
    ral.ctrl.tx_stretch_ctrl_en.set(1'b1);
    csr_update(ral.ctrl);
  endtask: initialization

  virtual task body();
    fork begin: iso_fork
      // Along with the target_runtime vseq body, spawn two processes that assist with checking in
      // this test. These will be killed when the body method concludes at the end of the test.
      fork
        super.body();
        count_edge_intr(TxStretch, tx_stretch_intr_poscnt, tx_stretch_intr_negcnt);
        forever begin
          // TP: Ensure that the target holds SCL low and does not continue the transfer until the
          //     TARGET_EVENTS.TX_PENDING bit has cleared.
          csr_spinwait(.ptr(ral.target_events.tx_pending), .exp_data(1'b1), .backdoor(1));
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.scl_io, 1'b0,
                       "Target-mode not holding SCL low while TX_PENDING.")
          fork begin: iso_fork2
            fork
              begin
                wait(cfg.m_i2c_agent_cfg.vif.scl_io !== 1'b0);
                `uvm_fatal(`gfn, "SCL was released while TX_PENDING was set!")
              end
              begin
                csr_spinwait(.ptr(ral.target_events.tx_pending), .exp_data(1'b0), .backdoor(1));
              end
            join_any
            disable fork;
          end: iso_fork2 join
        end
      join_any
      disable fork;
    end: iso_fork join
  endtask: body

  // This hook is called at the start of each new stimulus iteration.
  //
  virtual task setup_hook();
    // Cleanup for next iteration.
    tx_stretch_intr_poscnt = 0;
    tx_stretch_intr_negcnt = 0;
    transfer_cnt = 0;
  endtask

  virtual task start_of_stim_hook();
    // Write all rdata for the next read transaction to the TXFIFO
    while (read_rcvd.size() > 0) write_tx_fifo();
  endtask: start_of_stim_hook

  virtual task end_of_stim_hook();
    // Allow the interrupt handlers to wrap-up before the next
    // round of stimulus.
    #10us;
  endtask: end_of_stim_hook

  // Interrupt handler for the "cmd_complete" interrupt
  // (This overrides the parent class impl.)
  virtual task proc_intr_cmdcomplete();
    `uvm_info(`gfn, "proc_intr_cmdcomplete()", UVM_MEDIUM)

    transfer_cnt++;

    // We should have only had a single stretching event per transfer.
    `DV_CHECK_EQ(tx_stretch_intr_poscnt, transfer_cnt,
                 "tx_stretch interrupt didn't trigger correctly.")
    `DV_CHECK_EQ(tx_stretch_intr_negcnt, transfer_cnt,
                 "tx_stretch interrupt didn't trigger correctly.")

    // Simply acknowledge and clear this 'event'-type interrupt.
    clear_interrupt(CmdComplete, 0);
  endtask: proc_intr_cmdcomplete

  // Interrupt handler for the "tx_stretch" interrupt
  //
  // Desc:
  //   This test is directed such that we should be seeing stretching
  //   due to TX_STRETCH_CTRL_EN being set.
  //
  virtual task proc_intr_txstretch();
    `uvm_info(`gfn, "proc_intr_txstretch()", UVM_MEDIUM)

    // Check we have stretched due to the stretch_ctrl.
    csr_rd_check(.ptr(ral.target_events.tx_pending), .compare_value(1));

    `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.scl_io, 1'b0,
                 "Target-mode not holding SCL low while TX_PENDING.")
    `DV_CHECK_EQ(tx_stretch_intr_poscnt, transfer_cnt + 1,
                 "tx_stretch interrupt didn't trigger correctly.")
    `DV_CHECK_EQ(tx_stretch_intr_negcnt, transfer_cnt,
                 "tx_stretch interrupt deasserted when not expected.")

    // Clear the tx_pending bit to allow the transfer to proceed.
    ral.target_events.tx_pending.set(1'b1);
    csr_update(ral.target_events);

  endtask: proc_intr_txstretch

  // Interrupt handler for the 'acq_stretch' interrupt.
  //
  // Desc:
  //   This test configures the ACQFIFO watermark to zero, so this interrupt
  //   will be asserted every time a new entry to the fifo is pushed.
  //   As we wish to test tx-stretching due to the TX_STRETCH_CTRL feature, use
  //   this handler to prevent the ACQFIFO from filling past 1 entry, which
  //   would also cause the DUT to tx-stretch during read transactions.
  //
  virtual task proc_intr_acqthreshold();
    `uvm_info(`gfn, "proc_intr_acqthreshold()", UVM_MEDIUM)
    begin
      bit acq_fifo_empty;
      read_acq_fifo(.read_one(1), .acq_fifo_empty(acq_fifo_empty));
    end
  endtask: proc_intr_acqthreshold

endclass: i2c_target_tx_stretch_ctrl_vseq
