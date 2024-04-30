// Copyright lowRISC contributors (OpenTitan project).
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

  uint i2c_min_timeout           = 1;
  uint i2c_max_timeout           = 4;
  // maximum values for expected usage
  uint i2c_max_rx_thresh         = I2C_RX_FIFO_DEPTH - 1;
  uint i2c_max_fmt_thresh        = I2C_FMT_FIFO_DEPTH;
  uint i2c_max_acq_thresh        = I2C_ACQ_FIFO_DEPTH - 1;
  uint i2c_max_tx_thresh         = I2C_TX_FIFO_DEPTH;

  // bits to control fifos access
  // set en_rx_overflow to ensure ensure rx_overflow irq is triggered
  bit en_rx_overflow             = 1'b0;
  // set en_rx_threshold to ensure rx_threshold irq is triggered
  bit en_rx_threshold            = 1'b0;

  `uvm_object_new

endclass : i2c_seq_cfg
