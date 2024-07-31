// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence just adds a couple of additional constraints to prevent the generation of
// Isochronous transfers with the aim of exercising the more important configurations more
// thoroughly.
class usbdev_max_non_iso_usb_traffic_vseq extends usbdev_max_usb_traffic_vseq;
  `uvm_object_utils(usbdev_max_non_iso_usb_traffic_vseq)

  `uvm_object_new

  constraint out_non_iso_c {
    out_iso == 0;
  }
  constraint in_non_iso_c {
    in_iso == 0;
  }

  virtual task body;
    super.body();
  endtask
endclass : usbdev_max_non_iso_usb_traffic_vseq
