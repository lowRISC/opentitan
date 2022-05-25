// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// passthrough_mode test vseq
// SPI_HOST HWIP Technical Specification Block Diagram
class spi_host_passthrough_mode_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_passthrough_mode_vseq)
  `uvm_object_new

  virtual task pre_start();
    cfg.en_scb = 0;
    super.pre_start();
  endtask

  virtual task body();
    bit en = 1'b1;
    fork
    begin
      forever begin
        if(!en) break;
        @(posedge cfg.clk_rst_vif.clk);
        if (cfg.spi_passthrough_vif.passthrough_en) begin
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, cfg.spi_passthrough_vif.sck)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_en_o, cfg.spi_passthrough_vif.sck_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o, cfg.spi_passthrough_vif.csb)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o, cfg.spi_passthrough_vif.csb_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, cfg.spi_passthrough_vif.s_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_o, cfg.spi_passthrough_vif.is)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_i, cfg.spi_passthrough_vif.os)
        end else begin
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_en_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o, 1'b1)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_o, 4'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.os, 4'hf)
        end
      end
    end
    begin
      while (en) begin
        @(posedge cfg.clk_rst_vif.clk);
        cfg.spi_passthrough_vif.sck_en <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.csb_en <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.s_en   <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.csb    <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.sck    <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.is     <= $urandom_range(100, 2000);
        cfg.spi_passthrough_vif.cio_sd_i <= $urandom_range(100, 2000);
      end
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 20));
    end
    begin
      @(posedge cfg.clk_rst_vif.clk);
      for (int i = 0; i < (num_trans*num_runs); i++) begin
        @(posedge cfg.clk_rst_vif.clk);
        cfg.spi_passthrough_vif.passthrough_en <= $urandom_range(0, 1);
        cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      end
      en = 1'b0;
    end
    join
  endtask : body
endclass : spi_host_passthrough_mode_vseq
