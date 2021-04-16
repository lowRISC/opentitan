// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class spi_host_seq_cfg extends uvm_object;
  `uvm_object_utils(spi_host_seq_cfg)

  // knobs for number of requests sent to dut
  uint host_spi_min_trans             = 10;
  uint host_spi_max_trans             = 20;

  // knobs for number of retry after reset
  // for stress_all, error_intr, stress_all_with_rand_reset
  uint host_spi_min_runs              = 5;
  uint host_spi_max_runs              = 10;

  // knobs for dut's config registers
  uint host_spi_min_csn_hcyc          = 0;
  uint host_spi_max_csn_hcyc          = 15;
  uint host_spi_min_clkdiv            = 0;
  uint host_spi_max_clkdiv            = 15;
  uint host_spi_min_len               = 0;
  uint host_spi_max_len               = 15;
  uint host_spi_min_dly               = 0;
  uint host_spi_max_dly               = 5;
  uint host_spi_max_rxwm              = SPI_HOST_RX_DEPTH;
  uint host_spi_max_txwm              = SPI_HOST_TX_DEPTH;

  uint host_spi_min_num_wr_bytes      = 1;
  uint host_spi_max_num_wr_bytes      = SPI_HOST_TX_DEPTH;
  uint host_spi_min_num_rd_bytes      = 1;
  uint host_spi_max_num_rd_bytes      = SPI_HOST_RX_DEPTH;

  // scale factor, core clock is a random value
  // which is in range [bus_clk*(1-scale) : bus_clk*(1+scale)]
  real host_spi_clk_core_ratio        = 0.5;  // must be less than 1

  `uvm_object_new

endclass : spi_host_seq_cfg
