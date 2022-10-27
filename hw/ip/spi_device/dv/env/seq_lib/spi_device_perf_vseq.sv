// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test tx/rx sram fifo full by controlling the distribution of delay
// use less delay for tx write, regular delay for spi and the more delay for rx read
// use minimal delays for maximum performance
class spi_device_perf_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_perf_vseq)
  `uvm_object_new

  constraint tx_delay_c {
    tx_delay inside {[0 : 1]};
  }

  constraint rx_delay_c {
    rx_delay inside {[2 : 10]};
  }

  constraint num_trans_c {
    num_trans == 2;
  }

endclass : spi_device_perf_vseq
