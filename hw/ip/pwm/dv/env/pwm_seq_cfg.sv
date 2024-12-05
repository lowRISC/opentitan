// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.

class pwm_seq_cfg extends uvm_object;

  `uvm_object_utils(pwm_seq_cfg)
  `uvm_object_new

  // knobs for number of requests sent to dut
  uint pwm_min_num_trans         = 10;
  uint pwm_max_num_trans         = 15;

  // knobs for number of retry after reset
  // for stress_all, stress_all_with_rand_reset
  uint pwm_min_num_runs          = 1;
  uint pwm_max_num_runs          = 5;

  // knobs for pwm channels
  uint pwm_min_clk_div           = 1;
  uint pwm_max_clk_div           = 5;
  uint pwm_min_dc_resn           = 1;
  uint pwm_max_dc_resn           = 8;
  uint pwm_min_param             = 4;
  uint pwm_max_param             = 10;
  // derive params
  uint pwm_min_num_pulses        = 2 * pwm_min_param;
  uint pwm_max_num_pulses        = 4 * pwm_max_param;

  // test knobs
  int        pwm_run_channel     = PWM_NUM_CHANNELS;

endclass : pwm_seq_cfg
