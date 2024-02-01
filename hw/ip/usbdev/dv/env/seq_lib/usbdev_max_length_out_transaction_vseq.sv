// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Max length out transaction_vseq
class usbdev_max_length_out_transaction_vseq extends usbdev_random_length_out_transaction_vseq;
  `uvm_object_utils(usbdev_max_length_out_transaction_vseq)

  `uvm_object_new

  task pre_start();
    super.pre_start();
    randomize_length = 1'b0;
    num_of_bytes = 64;
  endtask
endclass
