// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_endp_acc test vseq
class usbdev_endp_acc_vseq extends usbdev_in_trans_vseq;
  `uvm_object_utils(usbdev_endp_acc_vseq)

  `uvm_object_new

  task body();
    // Perform OUT and IN transactions to all endpoints 1-11
    // Endpoint 0 is already tested
    void'($value$plusargs("endp=%0d", endp));
    `uvm_info(`gfn, $sformatf("Endpoint = %h\n",endp), UVM_DEBUG)
    super.body();
  endtask
endclass : usbdev_endp_acc_vseq
