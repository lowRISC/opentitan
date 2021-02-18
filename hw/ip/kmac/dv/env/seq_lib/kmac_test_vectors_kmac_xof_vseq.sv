// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_test_vectors_kmac_xof_vseq extends kmac_test_vectors_kmac_vseq;

  `uvm_object_utils(kmac_test_vectors_kmac_xof_vseq)
  `uvm_object_new

  virtual task pre_start();
    is_xof_test_vectors = 1;
    super.pre_start();
  endtask

endclass
