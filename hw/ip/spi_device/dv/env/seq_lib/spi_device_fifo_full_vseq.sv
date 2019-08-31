// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test tx/rx sram fifo full by controlling the distribution of delay
// use less delay for tx write, regular delay for spi and the more delay for rx read
class spi_device_fifo_full_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_fifo_full_vseq)
  `uvm_object_new

  // additional constraint for tx_total_bytes to transfer more data
  constraint tx_total_bytes_additional_c {
    tx_total_bytes inside {[5 * SRAM_SIZE : 10 * SRAM_SIZE]};
  }

  constraint tx_delay_c {
    tx_delay inside {[0 : 10]};
  }

  constraint rx_delay_c {
    rx_delay dist {
      0              :/ 1,
      [1   : 100]    :/ 1,
      [101 : 10_000] :/ 8
    };
  }

  constraint num_trans_c {
    num_trans inside {[2:3]};
  }

endclass : spi_device_fifo_full_vseq
