// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class i2c_seq_cfg extends uvm_object;
  `uvm_object_utils(i2c_seq_cfg)

  // Randomization weights in percentages, and other related settings.

  // TODO: This should move to `dv_base_seq_cfg`.
  // maximun number of times the vseq is randomized and rerun.
  uint min_num_trans     = 30;
  uint max_num_trans     = 50;

  // parameters configured at test level for *_vseq
  uint i2c_min_addr      = 0;
  uint i2c_max_addr      = 127;
  uint i2c_min_data      = 0;
  uint i2c_max_data      = 255;
  uint i2c_min_dly       = 0;
  uint i2c_max_dly       = 5;
  uint i2c_min_timing    = 1; // at least 1
  uint i2c_max_timing    = 5;
  uint i2c_time_range    = i2c_max_timing - i2c_min_timing;
  uint i2c_min_timeout   = 1;
  uint i2c_max_timeout   = 4;
  uint i2c_max_rxilvl    = 7;
  uint i2c_max_fmtilvl   = 3;

  `uvm_object_new

endclass : i2c_seq_cfg
