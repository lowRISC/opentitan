// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class i2c_seq_cfg extends uvm_object;
  `uvm_object_utils(i2c_seq_cfg)

  // knobs for number of requests sent to dut
  uint i2c_min_num_trans         = 10;
  uint i2c_max_num_trans         = 20;

  // knobs for number of retry after reset
  // for stress_all, error_intr, stress_all_with_rand_reset
  uint i2c_min_num_runs          = 5;
  uint i2c_max_num_runs          = 10;

  // knobs for dut's registers
  uint i2c_min_addr              = 0;
  uint i2c_max_addr              = 127;
  uint i2c_min_data              = 0;
  uint i2c_max_data              = 255;
  uint i2c_min_dly               = 0;
  uint i2c_max_dly               = 5;
  uint i2c_min_timing            = 1; // at least 1
  uint i2c_max_timing            = 5;
  uint i2c_time_range            = i2c_max_timing - i2c_min_timing;
  uint i2c_min_timeout           = 1;
  uint i2c_max_timeout           = 4;
  uint i2c_max_rxilvl            = 7;
  uint i2c_max_fmtilvl           = 3;

  // knobs for error_intr test
  // assertion probability of sda_interference, scl_interference, and
  // sda_unstable interrupts (in percentage)
  uint i2c_prob_sda_unstable     = 30;
  uint i2c_prob_sda_interference = 30;
  uint i2c_prob_scl_interference = 70;

  // bits to control fifos access
  // set en_fmt_overflow to ensure fmt_overflow irq is triggered
  bit en_fmt_overflow            = 1'b0;
  // set en_rx_overflow to ensure ensure rx_overflow irq is triggered
  bit en_rx_overflow             = 1'b0;
  // set en_rx_watermark to ensure rx_watermark irq is triggered
  bit en_rx_watermark            = 1'b0;

  // bits to control interference and unstable interrupts
  // set en_sda_unstable to allow sda_unstable irq is triggered
  bit en_sda_unstable            = 1'b0;
  // set en_scl_interference to allow scl_interference irq is triggered
  bit en_scl_interference        = 1'b0;
  // set en_sda_interference to allow sda_interference irq is triggered
  bit en_sda_interference        = 1'b0;

  `uvm_object_new

endclass : i2c_seq_cfg
