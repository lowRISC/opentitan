// Copyright lowRISC contributors.
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
  uint pwm_min_clk_div           = 0;
  uint pwm_max_clk_div           = 16;
  uint pwm_min_dc_resn           = 0;
  uint pwm_max_dc_resn           = 7;
  uint pwm_min_phase_delay       = 0;
  uint pwm_max_phase_delay       = 7;
  uint pwm_min_blink_param       = 0;
  uint pwm_max_blink_param       = 15;
  uint pwm_min_num_pulses        =  1;
  uint pwm_max_num_pulses        = 10;

  // ratio (<1) between minimum clk_core (core clock) and clk (bus clock)
  real pwm_core_clk_ratio        = 0.5;
endclass : pwm_seq_cfg
