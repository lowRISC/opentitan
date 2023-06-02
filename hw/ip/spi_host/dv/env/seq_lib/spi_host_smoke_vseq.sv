// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class spi_host_smoke_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)
  `uvm_object_new

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
  endtask : body

endclass : spi_host_smoke_vseq
