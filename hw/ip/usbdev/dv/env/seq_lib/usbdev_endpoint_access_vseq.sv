// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_endp_acc test vseq
class usbdev_endpoint_access_vseq extends usbdev_in_trans_vseq;
  `uvm_object_utils(usbdev_endpoint_access_vseq)

  `uvm_object_new

  task body();
    // Perform OUT and IN transactions to all endpoints 0-11
    // Extend from usbdev_in_trans b/c its doing OUT and IN to a specific endpoint number.
    for (endp = 0; endp <= 11; endp++) begin
      super.body();
    end
  endtask
endclass : usbdev_endpoint_access_vseq
