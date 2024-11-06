// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read IETF HMAC test vectors (used for the RFC4868 spec) and
// compare computed results with the expected values.

class hmac_test_vectors_hmac_vseq extends hmac_test_vectors_sha_vseq;
  `uvm_object_utils(hmac_test_vectors_hmac_vseq)

  // Constraints
  extern constraint hmac_enabled_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : hmac_test_vectors_hmac_vseq


constraint hmac_test_vectors_hmac_vseq::hmac_enabled_c {
  hmac_en == 1;
}

function hmac_test_vectors_hmac_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_test_vectors_hmac_vseq::body();
  // replace with HMAC NIST test vectors
  vector_list_256 = test_vectors_pkg::hmac_sha256_file_list;
  vector_list_384 = test_vectors_pkg::hmac_sha384_file_list;
  vector_list_512 = test_vectors_pkg::hmac_sha512_file_list;
  super.body();
endtask : body
