// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test starts a transaction, then deasserts the CONTROL.SPIEN bit
// mid-transaction.

class spi_host_spien_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_spien_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    // Ensure the command is long enough for us to stop in the middle of it.
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 6;
    cfg.seq_cfg.host_spi_min_num_seg = 4;
    cfg.seq_cfg.host_spi_max_num_seg = 8;
  endtask // pre_start

  virtual task body();
    spi_host_status_t status;

    fork start_agent_reactive_seqs(); join_none
    wait_ready_for_command();

    fork
      begin
        read_rx_fifo();
        // Read RXFIFO until STATUS.ACTIVE == 0
      end
      begin
        start_spi_host_trans(.num_transactions(3), .wait_ready(1));
        // Wait until the DUT has finished processing commands, and
        // the RXFIFO is empty (has been fully processed by the scoreboard).
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .timeout_ns(50_000_000));
        csr_spinwait(.ptr(ral.status.rxqd), .exp_data(8'h0));
        cfg.clk_rst_vif.wait_clks(100);
        // This thread should be the last to end.
      end
      do begin
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20000)); // clk_i cycles

        // Deassert CONTROL.SPIEN for a random length of time
        csr_wr(.ptr(ral.control.spien), .value(1'b0));
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20000));
        csr_wr(.ptr(ral.control.spien), .value(1'b1));

        // Break when STATUS.ACTIVE == 0
        csr_rd(.ptr(ral.status), .value(status), .backdoor(1));
      end while (status.active == 1);
    join

  endtask : body

endclass : spi_host_spien_vseq
