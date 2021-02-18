// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_test_vectors_sha3_vseq extends kmac_test_vectors_base_vseq;

  `uvm_object_utils(kmac_test_vectors_sha3_vseq)
  `uvm_object_new

  virtual task pre_start();
    case (cfg.sha3_variant)
      224: begin
        test_list = test_vectors_pkg::sha3_224_file_list;
      end
      256: begin
        test_list = test_vectors_pkg::sha3_256_file_list;
      end
      384: begin
        test_list = test_vectors_pkg::sha3_384_file_list;
      end
      512: begin
        test_list = test_vectors_pkg::sha3_512_file_list;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("%0d is not a valid sha3_variant", cfg.sha3_variant))
      end
    endcase
    super.pre_start();
  endtask

  virtual function void randomize_cfg(test_vectors_pkg::test_vectors_t vector);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(this,
      hash_mode == sha3_pkg::Sha3;
      if (cfg.sha3_variant == 224) {
        strength == sha3_pkg::L224;
      } else if (cfg.sha3_variant == 256) {
        strength == sha3_pkg::L256;
      } else if (cfg.sha3_variant == 384) {
        strength == sha3_pkg::L384;
      } else if (cfg.sha3_variant == 512) {
        strength == sha3_pkg::L512;
      }
      kmac_en == 0;
      output_len == vector.digest_length_byte;
    )
  endfunction

endclass
