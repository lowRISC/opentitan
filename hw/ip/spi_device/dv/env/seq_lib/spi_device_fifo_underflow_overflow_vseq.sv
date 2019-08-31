// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test tx sram fifo underflow and rx sram fifo overflow by overriding
// read_tx_filled_rx_space_bytes to send spi transfer when there is no space no data available
class spi_device_fifo_underflow_overflow_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_fifo_underflow_overflow_vseq)
  `uvm_object_new

  // return avail_bytes without checking the availability of sram fifo
  virtual task read_tx_filled_rx_space_bytes(ref uint avail_bytes);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_bytes,
                                       avail_bytes[1:0] == 0;
                                       avail_bytes dist {
                                           [1:SRAM_WORD_SIZE]    :/ 5,
                                           [SRAM_WORD_SIZE+1:20] :/ 20,
                                           [21:SRAM_SIZE-1]      :/ 1,
                                           SRAM_SIZE             :/ 1};)
  endtask

endclass : spi_device_fifo_underflow_overflow_vseq
