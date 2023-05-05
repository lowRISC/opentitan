// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_usbdev_stream_vseq extends chip_sw_usbdev_dpi_vseq;
  `uvm_object_utils(chip_sw_usbdev_stream_vseq)

  `uvm_object_new

  // TODO: introduce randomization to make this test more useful; candidates:
  // - number of endpoints
  // - response timing of DPI model
  // - stream test flags (transfer direction(s), variable/max-length packets...)

  virtual task body();
    super.body();
  endtask

endclass : chip_sw_usbdev_stream_vseq
