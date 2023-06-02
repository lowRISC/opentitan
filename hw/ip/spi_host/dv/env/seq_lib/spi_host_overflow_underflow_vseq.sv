// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error test vseq
// empty read error underflow
// write tx full fifo error overflow

class spi_host_overflow_underflow_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_overflow_underflow_vseq)
  `uvm_object_new

  spi_segment_item segment;
  int txfifo_ptr = 0;
  int segms_size;
  int segms_words;
  spi_host_command_t command[$];

  virtual task body();
    bit [7:0] read_q[$];
    bit [7:0] txqd;
    spi_host_intr_state_t intr_state;
    segms_size = 0;
    segms_words = 0;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;

     fork
      begin : isolation_fork
        fork
          start_agent_reactive_seqs();
        join_none
        begin
          wait_ready_for_command();
          start_spi_host_trans(num_trans);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));
          csr_spinwait(.ptr(ral.status.rxqd), .exp_data(8'h0));
          cfg.clk_rst_vif.wait_clks(100);
        end
        disable fork;
      end
      begin
        read_rx_fifo();
      end
    join

    access_data_fifo(read_q, RxFifo, 1'b0); // attempting empty read error underflow
    check_error(ral.error_status.underflow,1);

    csr_wr(.ptr(ral.configopts[0].clkdiv), .value(16'h28)); // clk div set to 20

    while (segms_words <= (SPI_HOST_TX_DEPTH + 1))  begin
      check_error(ral.error_status.overflow,0);
      gen_trans();
    end
    check_error(ral.error_status.overflow,1);
  endtask : body

  virtual task gen_trans();
    generate_transaction();
    segment = new();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        segms_size = segment.spi_data.size() + segms_size;
        segms_words = segms_size/4;
        access_data_fifo(segment.spi_data, TxFifo,0);
      end
      command.push_back(segment.command_reg);
    end
  endtask

  virtual task generate_transaction();
    transaction_init();
    transaction.tx_only_weight = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,num_segments == 1;cmd == ReadStd;)
  endtask

endclass : spi_host_overflow_underflow_vseq
