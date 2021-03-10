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
  uint host_spi_min_tx1               = 0;
  uint host_spi_max_tx1               = 15;
  uint host_spi_min_txn               = 0;
  uint host_spi_max_txn               = 15;
  uint host_spi_min_rx                = 0;
  uint host_spi_max_rx                = 15;
  uint host_spi_min_dummy             = 0;
  uint host_spi_max_dummy             = 15;
  uint host_spi_min_speed             = 0;
  uint host_spi_max_speed             = 2;
  uint host_spi_min_dly               = 0;
  uint host_spi_max_dly               = 5;
  uint host_spi_min_txwm              = 0;
  uint host_spi_max_txwm              = (1 << 9) - 1;
  uint host_spi_min_rxwm              = 0;
  uint host_spi_max_rxwm              = (1 << 7) - 1;

  // scale factor, core clock is a random value
  // which is in range [bus_clk*(1-scale) : bus_clk*(1+scale)]
  real host_spi_clk_core_ratio        = 0.5;  // must be less than 1

  `uvm_object_new

endclass : spi_host_seq_cfg
