// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_streaming_vseq extends usbdev_max_non_iso_usb_traffic_vseq;
  `uvm_object_utils(usbdev_streaming_vseq)

  `uvm_object_new

  // Ensure that a single endpoint pair (IN and OUT) is selected.
  constraint single_endpoint_c {
    ep_in_enabled != 0 && (ep_in_enabled & (ep_in_enabled - 1)) == 0;
  }

endclass : usbdev_streaming_vseq
