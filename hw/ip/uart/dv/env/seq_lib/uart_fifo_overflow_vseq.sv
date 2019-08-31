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

  // special handle for read rx when testing overflow
  virtual task rand_read_rx_byte(uint weight_to_skip);
    bit [TL_DW-1:0] status;

    csr_rd(.ptr(ral.status), .value(status));
    if (get_field_val(ral.status.rxfull, status)) begin
      // the rx item is abort to be completedly collected, don't know if drop it or not when rx fifo
      // is read at this period. Do not read at this cycle
      wait_when_in_ignored_period(.rx(1));
    end

    super.rand_read_rx_byte(weight_to_skip);
  endtask : rand_read_rx_byte

endclass : uart_fifo_overflow_vseq
