// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// performance test with 0 delay to access fifo, less delay to access interrupts
class uart_perf_vseq extends uart_fifo_full_vseq;
  `uvm_object_utils(uart_perf_vseq)

  `uvm_object_new

  constraint dly_to_access_fifo_c {dly_to_access_fifo == 0;}

  constraint dly_to_next_trans_c {dly_to_next_trans == 0;}

  constraint wait_for_idle_c {wait_for_idle == 0;}

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0 :/ 5,
      [1 : 100] :/ 4,
      [101 : 10_000] :/ 1
    };
  }

  // lower the freq as design freq isn't precise and agent has precise freq.
  // The delay in this test is small and running too fast will accumulate the diff, which may lead
  // to mis-aligned cycle
  constraint baud_rate_extra_c {baud_rate <= BaudRate230400;}

endclass : uart_perf_vseq
