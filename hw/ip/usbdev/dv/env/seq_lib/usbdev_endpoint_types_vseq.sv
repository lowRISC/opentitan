// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence designed to exercise all endpoint configurations and see that every type of endpoint
// encounters each of the possible transaction types (SETUP, OUT, IN and PRE).
class usbdev_endpoint_types_vseq extends usbdev_spray_packets_vseq;
  `uvm_object_utils(usbdev_endpoint_types_vseq)

  `uvm_object_new

  // For this sequence we are always targeting the DUT address.
  constraint target_addr_c {
    target_addr == dev_addr;
  }

endclass : usbdev_endpoint_types_vseq
