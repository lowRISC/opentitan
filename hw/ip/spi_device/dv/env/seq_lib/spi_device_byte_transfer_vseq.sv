// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Byte Access test to verify proper byte data transfer without timeout expiring
class spi_device_byte_transfer_vseq extends spi_device_rx_timeout_vseq;
  `uvm_object_utils(spi_device_byte_transfer_vseq)
  `uvm_object_new

  constraint timeout_place_c {
    timeout_place == 0;
  }

  constraint num_trans_c {
    num_trans == 10;
  }

endclass : spi_device_byte_transfer_vseq
