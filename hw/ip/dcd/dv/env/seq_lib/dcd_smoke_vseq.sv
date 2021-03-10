// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class dcd_smoke_vseq extends dcd_base_vseq;
  `uvm_object_utils(dcd_smoke_vseq)

  `uvm_object_new

  task body();
    `uvm_error(`gfn, "FIXME")
  endtask : body

endclass : dcd_smoke_vseq
