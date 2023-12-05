// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_smoke_vseq extends mbx_base_vseq;

  `uvm_object_utils(mbx_smoke_vseq)

  function new(string name = "mbx_smoke_vseq");
    super.new(name);
  endfunction : new

  virtual task body();
    `uvm_info(get_full_name(), "body -- smoke test -- Start", UVM_DEBUG)
    super.body();
    `uvm_info(get_full_name(), "body -- smoke test -- End", UVM_DEBUG)
  endtask : body

endclass : mbx_smoke_vseq
