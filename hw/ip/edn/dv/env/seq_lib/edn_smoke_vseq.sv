// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class edn_smoke_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_smoke_vseq)

  `uvm_object_new

  task body();
    // TODO: Temporary for creating edn environnment
    // Enable edn
    csr_wr(.csr(ral.ctrl), .value(1'b1));
  endtask : body

endclass : edn_smoke_vseq
