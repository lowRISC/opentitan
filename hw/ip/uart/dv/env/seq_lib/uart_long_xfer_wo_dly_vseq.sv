// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// transfer large amount of data without delay between each transaction, in order to test clock
// offset is not over 1/4 of the period
class uart_long_xfer_wo_dly_vseq extends uart_fifo_full_vseq;
  `uvm_object_utils(uart_long_xfer_wo_dly_vseq)

  `uvm_object_new

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      [101:1000] :/ 1
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      [101:1000] :/ 1
    };
  }

  constraint dly_to_access_fifo_c {
    dly_to_access_fifo < 100;
  }

  constraint dly_to_next_trans_c {
    dly_to_next_trans == 0;
  }

  constraint wait_for_idle_c {
    wait_for_idle == 0;
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 1: skip
    weight_to_skip_rx_read == 1;
  }

  constraint dly_to_rx_read_c {
    dly_to_rx_read < 100;
  }

  // lower the freq as design freq isn't precise and agent has precise freq.
  // The delay in this test is small and running too fast will accumulate the diff, which may lead
  // to mis-aligned cycle
  constraint baud_rate_extra_c {
    baud_rate > BaudRate230400;
  }

endclass : uart_long_xfer_wo_dly_vseq
