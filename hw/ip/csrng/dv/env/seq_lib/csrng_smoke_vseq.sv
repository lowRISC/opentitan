// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class csrng_smoke_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_smoke_vseq)

  `uvm_object_new

  task body();
    // TODO: Temporary for creating csrng environnment
    csr_rd_check(.ptr(ral.ctrl), .compare_value('h0));
  endtask : body

endclass : csrng_smoke_vseq
