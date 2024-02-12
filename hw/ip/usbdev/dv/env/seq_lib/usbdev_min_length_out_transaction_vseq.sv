// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Min length out transaction vseq
class usbdev_min_length_out_transaction_vseq extends usbdev_random_length_out_transaction_vseq;
  `uvm_object_utils(usbdev_min_length_out_transaction_vseq)

  `uvm_object_new

  task body();
    num_of_bytes = 0;
    rand_or_not = 0;
    super.body();
  endtask
endclass
