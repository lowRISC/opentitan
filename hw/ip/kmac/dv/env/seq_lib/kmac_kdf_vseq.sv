// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_kdf_vseq extends kmac_sideload_vseq;

  `uvm_object_utils(kmac_kdf_vseq)
  `uvm_object_new

  constraint kdf_c {
    // KDF outputs 256-bit digest (32 bytes)
    (kmac_en == 1) -> (output_len == 32);

    // KDF will never use XOF mode
    xof_en == 0;
  }

  // Bias kmac_en to be set more often,
  // KDF only applies to KMAC mode
  constraint kmac_en_c {
    kmac_en dist {
      0 :/ 3,
      1 :/ 7
    };
  }

  virtual task pre_start();
    en_kdf = 1;
    super.pre_start();
  endtask

endclass
