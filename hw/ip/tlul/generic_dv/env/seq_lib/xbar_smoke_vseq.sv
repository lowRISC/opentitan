// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequentially test each host to access any device
// device will respond in order
class xbar_smoke_vseq extends xbar_base_vseq;

  `uvm_object_utils(xbar_smoke_vseq)
  `uvm_object_new

  virtual task body();
    run_all_device_seq_nonblocking(.out_of_order_rsp(0));
    foreach (host_seq[i]) begin
      run_host_seq(i);
    end
  endtask

endclass
