// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Min length out transaction_vseq
class usbdev_min_length_out_transaction_vseq extends usbdev_random_length_out_transaction_vseq;
  `uvm_object_utils(usbdev_min_length_out_transaction_vseq)

  `uvm_object_new

  task pre_start();
    super.pre_start();

    randomize_length = 1'b0;
    num_of_bytes = 0;
  endtask
endclass
