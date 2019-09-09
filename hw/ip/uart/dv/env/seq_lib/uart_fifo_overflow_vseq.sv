// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_fifo_overflow_vseq extends uart_fifo_full_vseq;
  `uvm_object_utils(uart_fifo_overflow_vseq)

  `uvm_object_new

  // don't wait for fifo not full
  virtual task wait_for_tx_fifo_not_full();
  endtask : wait_for_tx_fifo_not_full

  // don't wait for fifo not full
  virtual task wait_for_rx_fifo_not_full();
  endtask : wait_for_rx_fifo_not_full

endclass : uart_fifo_overflow_vseq
