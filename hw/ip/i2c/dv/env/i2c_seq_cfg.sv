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
  uint i2c_min_timing            = 1; // at least 1
  uint i2c_max_timing            = 5;
  uint i2c_time_range            = i2c_max_timing - i2c_min_timing;
  uint i2c_min_timeout           = 1;
  uint i2c_max_timeout           = 4;
  // maximum values for expected usage
  uint i2c_max_rx_thresh         = I2C_RX_FIFO_DEPTH - 1;
  uint i2c_max_fmt_thresh        = I2C_FMT_FIFO_DEPTH;
  uint i2c_max_acq_thresh        = I2C_ACQ_FIFO_DEPTH - 1;
  uint i2c_max_tx_thresh         = I2C_TX_FIFO_DEPTH;

  // knobs for error_intr test
  // assertion probability of sda_interference, scl_interference, and
  // sda_unstable interrupts (in percentage)
  uint i2c_prob_sda_unstable     = 30;
  uint i2c_prob_sda_interference = 30;
  uint i2c_prob_scl_interference = 70;

  // bits to control fifos access
  // set en_rx_overflow to ensure ensure rx_overflow irq is triggered
  bit en_rx_overflow             = 1'b0;
  // set en_rx_threshold to ensure rx_threshold irq is triggered
  bit en_rx_threshold            = 1'b0;

  // bits to control interference and unstable interrupts
  // set en_sda_unstable to allow sda_unstable irq is triggered
  bit en_sda_unstable            = 1'b0;
  // set en_scl_interference to allow scl_interference irq is triggered
  bit en_scl_interference        = 1'b0;
  // set en_sda_interference to allow sda_interference irq is triggered
  bit en_sda_interference        = 1'b0;

  `uvm_object_new

  // Timing parameters of I2C for different speed modes in nanoseconds
  parameter uint TLOW_MINSTANDARD   = 4700;
  parameter uint THDSTA_MINSTANDARD = 4000;
  parameter uint TSUSTA_MINSTANDARD = 4700;
  parameter uint THDDAT_MINSTANDARD = 5000;
  parameter uint TSUDAT_MINSTANDARD = 250;
  parameter uint TBUF_MINSTANDARD   = 4700;
  parameter uint TSUSTO_MINSTANDARD = 4000;
  parameter uint TR_MINSTANDARD     = 10;
  parameter uint TF_MINSTANDARD     = 10;
  parameter uint THIGH_MINSTANDARD  = 4000;

  parameter uint TLOW_MINFAST       = 1300;
  parameter uint THDSTA_MINFAST     = 600;
  parameter uint TSUSTA_MINFAST     = 600;
  parameter uint THDDAT_MINFAST     = 0;
  parameter uint TSUDAT_MINFAST     = 100;
  parameter uint TBUF_MINFAST       = 1300;
  parameter uint TSUSTO_MINFAST     = 600;
  parameter uint TR_MINFAST         = 20;
  parameter uint TF_MINFAST         = 10;
  parameter uint THIGH_MINFAST      = 600;

  parameter uint TLOW_MINFASTPLUS   = 500;
  parameter uint THDSTA_MINFASTPLUS = 260;
  parameter uint TSUSTA_MINFASTPLUS = 260;
  parameter uint THDDAT_MINFASTPLUS = 0;
  parameter uint TSUDAT_MINFASTPLUS = 50;
  parameter uint TBUF_MINFASTPLUS   = 500;
  parameter uint TSUSTO_MINFASTPLUS = 260;
  parameter uint TR_MINFASTPLUS     = 10;
  parameter uint TF_MINFASTPLUS     = 10;
  parameter uint THIGH_MINFASTPLUS  = 260;

  parameter uint TR_MAXSTANDARD     = 1000;
  parameter uint TF_MAXSTANDARD     = 300;
  parameter uint TR_MAXFAST         = 300;
  parameter uint TF_MAXFAST         = 300;
  parameter uint TR_MAXFASTPLUS     = 120;
  parameter uint TF_MAXFASTPLUS     = 120;

  // Functions to calculate minimum timing parameters based on SCL frequency
  // scl_frequency : frequency of SCL in KHz
  // clk_period_ps : period of CLK input to DUT in picoseconds
  `ifndef I2C_GET_MIN_PARAM
  `define I2C_GET_MIN_PARAM(NAME_, PARAM_NAME_) \
      function uint get_``NAME_``_min(speed_mode_e speed_mode, uint clk_period_ps); \
        case (speed_mode) inside \
          Standard : return (1000* PARAM_NAME_``_MINSTANDARD/clk_period_ps); \
          Fast     : return (1000* PARAM_NAME_``_MINFAST/clk_period_ps); \
          FastPlus : return (1000* PARAM_NAME_``_MINFASTPLUS/clk_period_ps); \
        endcase \
      endfunction
  `endif

  // Functions to calculate maximum timing parameters based on SCL frequency
  // scl_frequency : frequency of SCL in KHz
  // clk_period_ps : period of CLK input to DUT in picoseconds
  `ifndef I2C_GET_MAX_PARAM
  `define I2C_GET_MAX_PARAM(NAME_, PARAM_NAME_) \
      function uint get_``NAME_``_max(speed_mode_e speed_mode, uint clk_period_ps); \
        case (speed_mode) inside \
          Standard : return (1000* PARAM_NAME_``_MAXSTANDARD/clk_period_ps); \
          Fast     : return (1000* PARAM_NAME_``_MAXFAST/clk_period_ps); \
          FastPlus : return (1000* PARAM_NAME_``_MAXFASTPLUS/clk_period_ps); \
        endcase \
      endfunction
  `endif

  `I2C_GET_MIN_PARAM(tlow, TLOW)
  `I2C_GET_MIN_PARAM(thdsta, THDSTA)
  `I2C_GET_MIN_PARAM(tsusta, TSUSTA)
  `I2C_GET_MIN_PARAM(thddat, THDDAT)
  `I2C_GET_MIN_PARAM(tsudat, TSUDAT)
  `I2C_GET_MIN_PARAM(tbuf, TBUF)
  `I2C_GET_MIN_PARAM(tsusto, TSUSTO)
  `I2C_GET_MIN_PARAM(tr, TR)
  `I2C_GET_MIN_PARAM(tf, TF)
  `I2C_GET_MIN_PARAM(thigh, THIGH)
  `I2C_GET_MAX_PARAM(tr, TR)
  `I2C_GET_MAX_PARAM(tf, TF)


endclass : i2c_seq_cfg
