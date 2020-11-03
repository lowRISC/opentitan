// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class edn_sanity_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_sanity_vseq)

  `uvm_object_new

  task body();
    // TODO: Temporary for creating edn environnment
    csr_rd_check(.ptr(ral.ctrl), .compare_value('h0));
  endtask : body

endclass : edn_sanity_vseq
