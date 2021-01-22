// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence assert reset randomly in between running timer

class rv_timer_random_reset_vseq extends rv_timer_random_vseq;
  `uvm_object_utils(rv_timer_random_reset_vseq)
  `uvm_object_new

  // assert reset randomly
  constraint assert_reset_c {
    assert_reset dist {
      0  := 1,
      1  := 2
    };
  }

endclass : rv_timer_random_reset_vseq
