// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_timer_max_vseq extends rv_timer_random_vseq;
  `uvm_object_utils(rv_timer_max_vseq)
  `uvm_object_new

  // Number of units for the counter to increment before producing an interrupt
  rand int unsigned gap_from_max;

  // Prescaler force to max.
  constraint prescale_c {
    foreach (prescale[i]) {
      prescale[i] == (2**PRESCALER_WIDTH-1);
    }
  }

  // Step forced to max
  constraint step_c {
    foreach (step[i]) {
      step[i] == (2**STEP_WIDTH-1);
    }
  }

  // Timer expiry needs to occur within reasonable amount of time (up to 5 cycles).
  constraint timer_exp_c {
    solve gap_from_max before timer_val;
    gap_from_max < 5;
    foreach (en_harts[i]) {
      timer_val[i] == (2**MTIME_WIDTH-1) - gap_from_max;
      foreach (en_timers[j]) {
        // Set to max
        compare_val[i][j] == (2**MTIME_WIDTH-1);
      }
    }
  }


endclass : rv_timer_max_vseq
