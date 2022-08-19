// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// set mode to FlashMode to test read buffer along with other intercept commands
class spi_device_flash_mode_vseq extends spi_device_intercept_vseq;
  `uvm_object_utils(spi_device_flash_mode_vseq)
  `uvm_object_new

  constraint device_mode_c {
    device_mode == FlashMode;
  }
endclass : spi_device_flash_mode_vseq
