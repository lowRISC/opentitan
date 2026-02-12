// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class spi_host_smoke_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)
  `uvm_object_new

  constraint spi_config_regs_c {
    // configopts regs
    spi_config_regs.cpol == 1'b0;
    spi_config_regs.cpha == 1'b0;
    spi_config_regs.csnlead == cfg.seq_cfg.host_spi_max_csn_latency;
    spi_config_regs.csntrail == cfg.seq_cfg.host_spi_max_csn_latency;
  }

  constraint spi_config_regs_clkdiv_c {
    spi_config_regs.clkdiv <= cfg.seq_cfg.host_spi_middle_clkdiv;
  }


  virtual task body();
    `uvm_info(`gfn, "Starting 'spi_host_smoke_vseq'", UVM_DEBUG)
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
        wait (num_rd > 0 || spi_host_txn_sent);
        // Only calling rd_rx_fifo if there are reads on the bus
        // otherwise `rd_rx_fifo` will lock up
        if (num_rd > 0)
          read_rx_fifo();
      end
    join
  endtask : body

endclass : spi_host_smoke_vseq
