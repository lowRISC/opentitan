// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// performance test vseq
class spi_host_performance_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_performance_vseq)
  `uvm_object_new

// constraints for simulation loops
  constraint num_trans_c {num_trans  == cfg.seq_cfg.host_spi_max_trans;}
  constraint intr_dly_c {clear_intr_dly == cfg.seq_cfg.host_spi_min_dly;}
  constraint fifo_dly_c {
    rx_fifo_access_dly == cfg.seq_cfg.host_spi_min_dly;
    tx_fifo_access_dly == cfg.seq_cfg.host_spi_min_dly;
  }

  constraint spi_config_regs_c {
      // configopts regs
      foreach (spi_config_regs.cpol[i]) {spi_config_regs.cpol[i] == 1'b0;}
      foreach (spi_config_regs.cpha[i]) {spi_config_regs.cpha[i] == 1'b0;}
      foreach (spi_config_regs.csnlead[i]) {
        spi_config_regs.csnlead[i] == cfg.seq_cfg.host_spi_min_csn_latency;
      }
      foreach (spi_config_regs.csntrail[i]) {
        spi_config_regs.csntrail[i] == cfg.seq_cfg.host_spi_min_csn_latency;
      }
      foreach (spi_config_regs.csnidle[i]) {
        spi_config_regs.csnidle[i] == cfg.seq_cfg.host_spi_min_csn_latency;
      }
      foreach (spi_config_regs.clkdiv[i]) {
        spi_config_regs.clkdiv[i] == cfg.seq_cfg.host_spi_min_clkdiv;
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
          cfg.clk_rst_vif.wait_clks(100);
        end
        disable fork;
      end
      begin
        read_rx_fifo();
      end
    join
  endtask : body

  virtual task start_spi_host_trans(int num_transactions, bit wait_ready = 1'b1);
    cfg.seq_cfg.std_en  = 1;
    cfg.seq_cfg.dual_en = 1;
    cfg.seq_cfg.quad_en = 1;
    super.start_spi_host_trans(num_trans);
  endtask

  virtual task generate_transaction();
    transaction_init();
    transaction.tx_only_weight = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,num_segments == 1;cmd == ReadStd;)
  endtask

endclass : spi_host_performance_vseq
