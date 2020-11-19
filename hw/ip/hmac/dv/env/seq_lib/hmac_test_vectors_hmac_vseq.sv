// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read hmac vectors and compare the expected value

class hmac_test_vectors_hmac_vseq extends hmac_test_vectors_sha_vseq;
  `uvm_object_utils(hmac_test_vectors_hmac_vseq)
  `uvm_object_new

  task body();
    hmac_en = 1'b1;
    vector_list = test_vectors_pkg::hmac_file_list;
    super.body();
  endtask

endclass : hmac_test_vectors_hmac_vseq
