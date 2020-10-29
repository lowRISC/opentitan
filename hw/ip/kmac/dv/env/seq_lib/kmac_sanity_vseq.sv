// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class kmac_sanity_vseq extends kmac_base_vseq;
  `uvm_object_utils(kmac_sanity_vseq)

  `uvm_object_new

  task body();
  endtask : body

endclass : kmac_sanity_vseq
