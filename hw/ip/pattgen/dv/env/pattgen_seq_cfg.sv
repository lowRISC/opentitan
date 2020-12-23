// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class pattgen_seq_cfg extends uvm_object;
  `uvm_object_utils(pattgen_seq_cfg)
  `uvm_object_new

  // knobs for number of requests sent to dut
  uint pattgen_min_num_trans         = 20;
  uint pattgen_max_num_trans         = 30;

  // knobs for number of retry after reset
  // for stress_all, stress_all_with_rand_reset
  uint pattgen_min_num_runs          = 5;
  uint pattgen_max_num_runs          = 10;

  // knobs for pattgen channel
  uint pattgen_min_dly               = 0;
  uint pattgen_max_dly               = 5;

  // see the specification document, the effective values of prediv, len, and reps
  // are incremented from the coresponding register values
  uint pattgen_min_prediv            = 0;
  uint pattgen_max_prediv            = 20;
  uint pattgen_min_len               = 0;
  uint pattgen_max_len               = 10;
  uint pattgen_min_reps              = 0;
  uint pattgen_max_reps              = 10;

  uint pattgen_low_polarity_pct      = 50;  // in percentage
  uint pattgen_sync_channels_pct     = 30;  // in percentage

  // for error_vseq
  bit  error_injected_enb            = 1'b0;
  uint error_injected_pct            = 50;  // in percentage

endclass : pattgen_seq_cfg
