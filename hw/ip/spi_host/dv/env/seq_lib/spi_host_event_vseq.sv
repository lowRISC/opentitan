// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// event test vseq
// sequence verifies all events occur in event_enable register
class spi_host_event_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_event_vseq)
  `uvm_object_new

  bit rx_drain;
  bit [7:0] rxqd;
  bit [7:0] txqd;
  spi_segment_item segment;
  spi_host_intr_state_t intr_state;
  int segms_size;
  int segms_words;
  spi_host_command_t command[$];
  spi_host_command_t command_snd;

  // TODO - to be removed when issue #12262
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

  constraint spi_host_command_reg_c {
    spi_host_command_reg.direction == Bidir;
    spi_host_command_reg.mode == Standard;
  }

  virtual task body();
    segms_size = 0;
    segms_words = 0;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
    wait_ready_for_command();
    program_spi_host_regs();
    check_event(ral.status.ready, 1);

    while (segms_words <=  spi_host_ctrl_reg.tx_watermark)  begin
      gen_trans();
    end
    check_event(ral.status.txwm,0);
    for (int i = 0; i < command.size(); i++) begin
      command_snd = command[i];
      snd_cmd(command_snd);
      if(i == 0) check_event(ral.status.active, 1);
      csr_rd(.ptr(ral.status.txqd), .value(txqd));
      if (txqd < spi_host_ctrl_reg.tx_watermark) begin
        check_event(ral.status.txwm, 1);
      end
    end
    read_rx_fifo();
    check_event(ral.status.txempty, 1);

    cfg.clk_rst_vif.wait_clks(100);

    fork
      begin : isolation_fork
        fork
          start_reactive_seq();
        join_none

        begin
          for (int i = 0; i < spi_host_ctrl_reg.rx_watermark; i++) begin
            check_event(ral.status.rxwm, 0);
            if (i < spi_host_ctrl_reg.rx_watermark -1) check_event(ral.status.rxwm, 0);
            spi_send_trans(1);
            csr_spinwait(.ptr(ral.status.txqd), .exp_data(0));
            csr_spinwait(.ptr(ral.status.rxqd), .exp_data(i+1));
          end
          check_event(ral.status.rxwm, 1);
          if (spi_host_ctrl_reg.rx_watermark > 0) read_rx_fifo();
          for (int i = 0; i < SPI_HOST_RX_DEPTH; i++) begin
            check_event(ral.status.rxfull, 0);
            if (i < SPI_HOST_RX_DEPTH - 1) check_event(ral.status.rxfull, 0);
            spi_send_trans(1);
            csr_spinwait(.ptr(ral.status.txqd), .exp_data(0));
            csr_spinwait(.ptr(ral.status.rxqd), .exp_data(i+1));
          end
          check_event(ral.status.rxfull, 1);
          read_rx_fifo();
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
        access_data_fifo(segment.spi_data, TxFifo);
      end
      command.push_back(segment.command_reg);
    end
  endtask

  virtual task snd_cmd(spi_host_command_t command_snd);
    wait_ready_for_command();
    program_command_reg(command_snd);
    wait_ready_for_command();
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
endclass : spi_host_event_vseq
