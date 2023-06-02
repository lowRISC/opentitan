// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error_cmd test vseq
// test tries to capture error interrupt when cmd invalid condition appears
// cmd invalid is created when cmd sent and host isnt ready
class spi_host_status_stall_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_status_stall_vseq)
  `uvm_object_new

  bit [7:0] rxqd;
  spi_host_command_t command_q[$];
  spi_segment_item segment_q[$];

  virtual task body();
    spi_host_command_t command_snd;
    spi_segment_item segment_snd;
    bit [7:0] read_q[$];

    begin : isolation_fork
      fork
        start_agent_reactive_seqs();
      join_none

      begin
        program_spi_host_regs();
        while (rxqd < SPI_HOST_RX_DEPTH) begin
          spi_rd_trans();
          if (rxqd == SPI_HOST_RX_DEPTH) begin
            break;
          end else begin
            check_event(ral.status.rxfull, 0, 0);
            csr_rd_check(.ptr(ral.status.rxstall), .compare_value(1'b0));
          end
        end
      end
      disable fork;
    end : isolation_fork
    csr_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b1));
    csr_spinwait(.ptr(ral.status.rxstall), .exp_data(1'b1));
    for (int i = 0; i < SPI_HOST_RX_DEPTH; i++) begin
      access_data_fifo(read_q, RxFifo);
    end
    // send transaction to check tx stall
    cfg.tx_stall_check = 1'b1;
    wr_trans();
    command_snd = command_q[0];
    spi_wr_trans_cmd(command_snd);
    csr_spinwait(.ptr(ral.status.txstall), .exp_data(1'b1));
    segment_snd = segment_q[0];
    spi_wr_trans_seg(segment_snd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));
    csr_spinwait(.ptr(ral.status.txqd), .exp_data(0));
    cfg.clk_rst_vif.wait_clks(100);
    read_rx_fifo();

  endtask : body

  virtual task spi_rd_trans(bit wait_ready = 1'b1);
    if (wait_ready) wait_ready_for_command();
    generate_transaction_stall();
    rd_trans(transaction, wait_ready);
  endtask

  virtual task rd_trans(spi_transaction_item trans, bit wait_ready = 1'b1);
    spi_segment_item segment;
    while ((trans.segments.size() > 0)  && (!(rxqd == SPI_HOST_RX_DEPTH))) begin
      // wait on DUT ready
      segment = trans.segments.pop_back();
      if (wait_ready) wait_ready_for_command();
      // lock fifo to this seq
      spi_host_atomic.get(1);
      // write data to fifo
      if (segment.command_reg.direction != RxOnly) begin
        access_data_fifo(segment.spi_data, TxFifo);
      end
      program_command_reg(segment.command_reg);
      spi_host_atomic.put(1);
      csr_rd(.ptr(ral.status.rxqd), .value(rxqd));
    end
  endtask : rd_trans

  virtual task generate_transaction_stall(bit readonly = 1'b1);
    transaction_init();
    if (readonly) begin
      transaction.tx_only_weight = 0;
      `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
         num_segments == 1;cmd == ReadStd;)
    end else begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
         num_segments == 1;cmd == WriteStd;)
    end
  endtask

  virtual task wr_trans();
    spi_segment_item segment;
    generate_transaction_stall(.readonly(0));
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      wait_ready_for_command();
      command_q.push_back(segment.command_reg);
      segment_q.push_back(segment);
    end
  endtask : wr_trans

  virtual task spi_wr_trans_cmd(spi_host_command_t command_snd);
    wait_ready_for_command();
    program_command_reg(command_snd);
  endtask

  virtual task spi_wr_trans_seg(spi_segment_item segment_snd);
    if (segment_snd.command_reg.direction != RxOnly) begin
      access_data_fifo(segment_snd.spi_data, TxFifo);
    end
  endtask

endclass : spi_host_status_stall_vseq
