// Copyright lowRISC contributors (OpenTitan project).
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

  constraint dly_to_next_rx_trans_c {
    dly_to_next_rx_trans dist {
      0           :/ RxFifoDepth - 2,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint dly_to_next_tx_trans_c {
    dly_to_next_tx_trans dist {
      0           :/ TxFifoDepth - 2,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint wait_for_rx_idle_c {
    // ratio of wait/not_wait depends upon RxFifoDepth to ensure we're very likely to get a run
    // of transactions to fill the FIFO
    wait_for_rx_idle dist {
      1       :/ 1,
      0       :/ RxFifoDepth + 10
    };
  }

  constraint wait_for_tx_idle_c {
    // ratio of wait/not_wait depends upon TxFifoDepth to ensure we're very likely to get a run
    // of transactions to fill the FIFO
    wait_for_tx_idle dist {
      1       :/ 1,
      0       :/ TxFifoDepth + 10
    };
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 50: skip
    weight_to_skip_rx_read == 50;
  }

  `uvm_object_new

endclass : uart_fifo_full_vseq
