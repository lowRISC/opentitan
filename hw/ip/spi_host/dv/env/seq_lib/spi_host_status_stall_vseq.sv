// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Force the DUT to stall on both a rx and a tx transaction.
// This occurs when the RXFIFO and TXFIFO are full/empty respectively, and we
// try to continue a transaction.
// First create read transactions, without emptying the fifo, until we see rxfull
// and rxstall.
// Then, create a write transaction without adding data to the txfifo, and check
// for txempty and txstall.
class spi_host_status_stall_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_status_stall_vseq)
  `uvm_object_new

  bit [7:0] rxqd;
  spi_host_command_t command_q[$];
  spi_segment_item segment_q[$];

  virtual task pre_start();
    // Force more segments so we can fill the RXFIFO faster.
    cfg.seq_cfg.host_spi_min_num_seg = 4;
    cfg.seq_cfg.host_spi_max_num_seg = 8;
    super.pre_start();
  endtask : pre_start;

  virtual task body();
    spi_host_command_t command_snd;
    bit [7:0] read_q[$];

    // Generate read transactions without accesing RXFIFO until we get an rxstall
    begin : isolation_fork
      // Start the agent sequences to provide (random) response data to our reads.
      fork start_agent_reactive_seqs(); join_none
      begin
        program_spi_host_regs();
        while (rxqd < SPI_HOST_RX_DEPTH) begin
          wait_ready_for_command();
          generate_stall_transaction();
          rd_trans(transaction);
          if (rxqd == SPI_HOST_RX_DEPTH) break;
          else begin
            // If we have not yet filled the RXFIFO, confirm that the DUT does
            // not indicate rxfull or rxstall.
            check_event(ral.status.rxfull, 0, 0);
            csr_rd_check(.ptr(ral.status.rxstall), .compare_value(1'b0));
          end
        end
      end
      disable fork;
    end : isolation_fork
    // Check that rxfull and rxstall events are set now that the
    // RXQD has indicated we are full.
    csr_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b1));
    csr_spinwait(.ptr(ral.status.rxstall), .exp_data(1'b1));
    // Check complete, clear all data from the RXFIFO, allowing the txn to complete.
    read_rx_fifo();

    // Now, send a new write transaction, without any data in TXFIFO, to check txstall
    begin : create_txstall_txempty
      spi_segment_item segment_snd;
      cfg.tx_stall_check = 1'b1;

      generate_stall_transaction(.readonly(0));
      $cast(segment_snd, transaction.segments[$].clone());
      wait_ready_for_command();
      program_command_reg(segment_snd.command_reg);
      // Now wait until the DUT asserts it's stall output.
      csr_spinwait(.ptr(ral.status.txstall), .exp_data(1'b1));
      // Now put some data into the TXFIFO, allowing the command to complete.
      access_data_fifo(segment_snd.spi_data, TxFifo);
      csr_spinwait(.ptr(ral.status.cmdqd), .exp_data(0));
      csr_spinwait(.ptr(ral.status.active), .exp_data(0));
      cfg.tx_stall_check = 1'b0;
    end : create_txstall_txempty

    begin : test_recovery_with_smoketest
      uvm_sequence seq = create_seq_by_name("spi_host_smoke_vseq");
      seq.set_sequencer(p_sequencer);
      cfg.seq_cfg.host_spi_min_trans = 1;
      cfg.seq_cfg.host_spi_max_trans = 2;
      `DV_CHECK_RANDOMIZE_FATAL(seq)
      seq.start(p_sequencer);
    end

    cfg.clk_rst_vif.wait_clks(1000);
    csr_spinwait(.ptr(ral.status.active), .exp_data(0));
    // If needed, read out any remaining RXFIFO data for the scb before ending.
    begin : clear_rxfifo
      spi_host_status_t status;
      csr_rd(.ptr(ral.status), .value(status));
      if (status.rx_qd != 0) read_rx_fifo();
    end
    cfg.clk_rst_vif.wait_clks(1000);

  endtask : body

  // Drive all segments of the read transaction. Return when we run out of
  // segments, or the RXQD indicates we are full.
  virtual task rd_trans(spi_transaction_item trans, bit wait_ready = 1'b1);
    spi_segment_item segment;
    while ((trans.segments.size() > 0)  && (!(rxqd == SPI_HOST_RX_DEPTH))) begin
      if (wait_ready) wait_ready_for_command();

      // Lock fifo to this task, write any data to TXFIFO if required, write COMMAND csr starts txn.
      spi_host_atomic.get(1); begin : locked_fifo_access
        segment = trans.segments.pop_back();
        if (segment.command_reg.direction != RxOnly) begin
          access_data_fifo(segment.spi_data, TxFifo);
        end
        program_command_reg(segment.command_reg);
      end spi_host_atomic.put(1);

      csr_rd(.ptr(ral.status.rxqd), .value(rxqd));
    end
  endtask : rd_trans

  // Randomize the transaction item to allow us to create stalls.
  virtual task generate_stall_transaction(bit readonly = 1'b1);
    transaction_init();
    if (readonly) begin
      transaction.tx_only_weight = 0;
      `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
         cmd == ReadStd;)
    end else begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
         cmd == WriteStd;)
    end
  endtask : generate_stall_transaction

endclass : spi_host_status_stall_vseq
