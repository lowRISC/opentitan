// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error test vseq
// empty read error underflow
// write tx full fifo error overflow

class spi_host_error_txrx_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_error_txrx_vseq)
  `uvm_object_new

  spi_segment_item segment;
  int txfifo_ptr = 0;
  int segms_size;

constraint spi_config_regs_c {
      // configopts regs
      foreach (spi_config_regs.cpol[i]) {spi_config_regs.cpol[i] == 1'b0;}
      foreach (spi_config_regs.cpha[i]) {spi_config_regs.cpha[i] == 1'b0;}
      foreach (spi_config_regs.csnlead[i]) {
        spi_config_regs.csnlead[i] == cfg.seq_cfg.host_spi_max_csn_latency;
      }
      foreach (spi_config_regs.csntrail[i]) {
        spi_config_regs.csntrail[i] == cfg.seq_cfg.host_spi_max_csn_latency;
      }
      foreach (spi_config_regs.csnidle[i]) {
        spi_config_regs.csnidle[i] == cfg.seq_cfg.host_spi_max_csn_latency;
      }
      foreach (spi_config_regs.clkdiv[i]) {
        spi_config_regs.clkdiv[i] == cfg.seq_cfg.host_spi_max_clkdiv;
      }
  }

  virtual task body();
    bit [7:0] read_q[$];
    bit [7:0] txqd;
    spi_host_intr_state_t intr_state;

     fork
      begin : isolation_fork
        fork
          start_reactive_seq();
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
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
    // loop for depth X no of bytes and 5 words short of SPI_HOST_TX_DEPTH
    while(txfifo_ptr < ((SPI_HOST_TX_DEPTH*4)-4)) begin
      segms_size = 0;
      if(txfifo_ptr < ((SPI_HOST_TX_DEPTH*4)-4)) begin
        check_error(ral.error_status.overflow, 0);
      end else begin
        check_error(ral.error_status.overflow, 1);
      end
      gen_txn_filltx();
      txfifo_ptr = segms_size + txfifo_ptr;
      `uvm_info(`gfn, $sformatf("\n txfifo_ptr Value %d",txfifo_ptr), UVM_LOW)
      program_command_reg(segment.command_reg);
    end // end while

    gen_txn_filltx(0); // segsize not incremented
    check_error(ral.error_status.overflow,1);
  endtask : body

  task gen_txn_filltx(bit do_seqsize_increase = 1);
    generate_transaction();
    segment = new();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        if(do_seqsize_increase) segms_size = segment.spi_data.size() + segms_size;
        access_data_fifo(segment.spi_data, TxFifo,1'b0); // write tx fifo to overflow
      end
    end
  endtask:gen_txn_filltx

endclass : spi_host_error_txrx_vseq
