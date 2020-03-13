// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test tx/rx sram fifo with extreme setting, size 1 word and SRAM_SIZE-1 word
class spi_device_extreme_fifo_size_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_extreme_fifo_size_vseq)
  `uvm_object_new

  constraint sram_size_constraints_c {
    num_host_sram_words dist {
      1 :/ 1,                     // 1 word
      SRAM_SIZE[31:2]/2     :/ 1, // half of the total mem
      SRAM_SIZE[31:2]-1     :/ 1, // max size
      [2:SRAM_SIZE[31:2]-2] :/ 1
    };
    num_device_sram_words dist {
      1 :/ 1,                     // 1 word
      SRAM_SIZE[31:2]/2     :/ 1, // half of the total mem
      SRAM_SIZE[31:2]-1     :/ 1, // max size
      [2:SRAM_SIZE[31:2]-2] :/ 1
    };
  }

  // reduce total data to reduce sim time as fifo size is too small and it takes much longer time
  // to finish
  constraint tx_total_bytes_c {
    tx_total_bytes inside {[SRAM_SIZE/2 : SRAM_SIZE*2]};
    tx_total_bytes[1:0] == 0; // word aligned
  }

  constraint num_trans_c {
    num_trans == 2;
  }
endclass : spi_device_extreme_fifo_size_vseq
