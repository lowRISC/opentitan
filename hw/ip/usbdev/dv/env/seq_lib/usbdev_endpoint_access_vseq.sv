// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_endp_acc test vseq
class usbdev_endpoint_access_vseq extends usbdev_in_trans_vseq;
  `uvm_object_utils(usbdev_endpoint_access_vseq)

  `uvm_object_new

  task body();
    // Perform OUT and IN transactions to all supported endpoints.
    //
    // Extend from usbdev_in_trans because it's doing OUT and IN traffic to a specific endpoint
    // number, so this covers all endpoints.
    for (ep_default = 0; ep_default < NEndpoints; ep_default++) begin
      super.body();
    end
  endtask
endclass : usbdev_endpoint_access_vseq
