// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_vseq extends kmac_sideload_vseq;

  `uvm_object_utils(kmac_app_vseq)
  `uvm_object_new

  constraint app_c {
    if (kmac_en) {
      // KMAC_APP outputs 256-bit digest (32 bytes)
      output_len == 32;

      // application interface locked at 256-bit strength
      strength == sha3_pkg::L256;
    }

    // KMAC_APP will never use XOF mode
    xof_en == 0;
  }

  // Bias kmac_en to be set more often,
  // KMAC_APP only applies to KMAC mode
  constraint kmac_en_c {
    kmac_en dist {
      0 :/ 3,
      1 :/ 7
    };
  }

  virtual task pre_start();
    en_app = 1;
    super.pre_start();
  endtask

endclass
