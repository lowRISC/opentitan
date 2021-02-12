// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_test_vectors_kmac_vseq extends kmac_test_vectors_base_vseq;

  `uvm_object_utils(kmac_test_vectors_kmac_vseq)
  `uvm_object_new

  bit is_xof_test_vectors = 0;

  virtual task pre_start();
    test_list = (is_xof_test_vectors) ? test_vectors_pkg::kmac_xof_file_list :
                                        test_vectors_pkg::kmac_file_list;
    custom_str_len_c.constraint_mode(0);
    super.pre_start();
  endtask

  virtual function void randomize_cfg(test_vectors_pkg::test_vectors_t vector);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(this,
      hash_mode == sha3_pkg::CShake;
      kmac_en == 1;
      xof_en == is_xof_test_vectors;
      output_len == vector.digest_length_byte;
      if (vector.security_strength == 128) {
        strength == sha3_pkg::L128;
      } else if (vector.security_strength == 256) {
        strength == sha3_pkg::L256;
      }
      // set key_len CSR
      if (vector.key_length_word * 32 == 128) {
        key_len == Key128;
      } else if (vector.key_length_word * 32 == 192) {
        key_len == Key192;
      } else if (vector.key_length_word * 32 == 256) {
        key_len == Key256;
      } else if (vector.key_length_word * 32 == 384) {
        key_len == Key384;
      } else if (vector.key_length_word * 32 == 512) {
        key_len == Key512;
      }
      custom_str_len == vector.customization_str.len();
    )
  endfunction

endclass
