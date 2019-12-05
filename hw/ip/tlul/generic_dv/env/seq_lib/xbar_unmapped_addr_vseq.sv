// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// allow host to drive unmapped addr
// expect xbar will return d_error=1 and won't pass it to any device
class xbar_unmapped_addr_vseq extends xbar_random_vseq;

  `uvm_object_utils(xbar_unmapped_addr_vseq)
  `uvm_object_new

  // allow host to driver unmapped addr
  virtual function void update_host_seq();
    foreach (host_seq[i]) begin
      host_seq[i].en_unmapped_addr = 1;
    end
  endfunction

endclass
