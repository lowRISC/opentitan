// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error_cmd test vseq
// test tries to capture error interrupt when cmd invalid condition appears
// cmd invalid is created when cmd sent and host isnt ready
class spi_host_error_cmd_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_error_cmd_vseq)
  `uvm_object_new

  spi_segment_item segment;
  int cmdq_depth = 0;

  virtual task body();
    program_spi_host_regs();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
    while (cmdq_depth <= (SPI_HOST_CMD_DEPTH )) begin
      check_error(ral.error_status.cmdbusy, 0);
      send_cmd();
    end
    check_error(ral.error_status.cmdbusy, 1);
  endtask : body

  virtual task send_cmd();
    generate_transaction();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        access_data_fifo(segment.spi_data, TxFifo);
      end
    end
    program_command_reg(segment.command_reg);
    cmdq_depth++;
  endtask

  virtual task generate_transaction();
    transaction_init();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,num_segments == 1;cmd == ReadStd;)
  endtask

endclass : spi_host_error_cmd_vseq
