// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error_cmd test vseq
// test tries to capture error interrupt when cmd invalid condition appears
// cmd invalid is created when cmd sent and host isnt ready
class spi_host_status_stall_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_status_stall_vseq)
  `uvm_object_new

  bit rx_drain;
  bit [7:0] rxqd;
  bit [7:0] txqd;
  spi_segment_item segment;
  spi_host_intr_state_t intr_state;
  int segms_size;
  int segms_words;
  spi_host_command_t command[$];
  bit [7:0] spi_data_gen[$];
  spi_host_command_t command_snd;

  virtual task body();

    segms_size = 0;
    segms_words = 0;

    fork
      begin : isolation_fork
        fork
          start_reactive_seq();
        join_none

        begin
          wait_ready_for_command();
          start_spi_host_trans(10);
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

    gen_trans();
    command_snd = command[0];
    snd_cmd(command_snd);
    csr_rd_check(.ptr(ral.status.txstall), .compare_value(1'b1));
    cfg.clk_rst_vif.wait_clks(100);

    fork
      begin : isolation_fork1
        fork
          start_reactive_seq();
        join_none

        begin
          for (int i = 0; i < SPI_HOST_RX_DEPTH; i++) begin
            check_event(ral.status.rxfull, 0);
            if (i < SPI_HOST_RX_DEPTH - 1) check_event(ral.status.rxfull, 0);
            spi_send_trans(1);
            csr_spinwait(.ptr(ral.status.txqd), .exp_data(0));
            csr_spinwait(.ptr(ral.status.rxqd), .exp_data(i+1));
          end
          check_event(ral.status.rxfull, 1);
          spi_send_trans(1);
          csr_rd_check(.ptr(ral.status.rxstall), .compare_value(1'b1));
        end

        disable fork;
      end
    join
  endtask : body

  virtual task gen_trans();
    generate_transaction();
    segment = new();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        segms_size = segment.spi_data.size() + segms_size;
        segms_words = segms_size/4;
      end
      command.push_back(segment.command_reg);
    end
  endtask

  virtual task snd_cmd(spi_host_command_t command_snd);
    wait_ready_for_command();
    program_command_reg(command_snd);
  endtask

  virtual task spi_send_trans(int num_transactions, bit wait_ready = 1'b1);
    for (int n = 0; n < num_transactions; n++) begin
      generate_transaction();
      send_trans(transaction, wait_ready);
      if (wait_ready) wait_ready_for_command();
    end
  endtask

  virtual task generate_transaction();
    transaction_init();
    transaction.tx_only_weight = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,num_segments == 1;cmd == ReadStd;)
  endtask
endclass : spi_host_status_stall_vseq
