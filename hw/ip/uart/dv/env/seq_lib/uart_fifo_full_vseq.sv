// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_fifo_full_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_fifo_full_vseq)

  constraint num_trans_c {
    num_trans inside {[5:10]};
  }

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      [0:1]    :/ 2,
      [2:32]   :/ 2,
      [33:100] :/ 2
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      [0:1]    :/ 2,
      [2:32]   :/ 2,
      [33:100] :/ 2
    };
  }

  constraint dly_to_next_trans_c {
    dly_to_next_trans dist {
      0           :/ 30,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint wait_for_idle_c {
    // fifo is 32 depth, wait/not_wait = 1/40, higher change to have fifo full
    wait_for_idle dist {
      1       :/ 1,
      0       :/ 40
    };
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 50: skip
    weight_to_skip_rx_read == 50;
  }

  `uvm_object_new

endclass : uart_fifo_full_vseq
