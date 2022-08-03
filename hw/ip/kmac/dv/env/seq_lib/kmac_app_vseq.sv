// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_vseq extends kmac_sideload_vseq;

  `uvm_object_utils(kmac_app_vseq)
  `uvm_object_new

  constraint en_app_c {
    en_app dist {
      0 :/ 3,
      1 :/ 7
    };
  }

  // msg size when using app interface must be non-zero
  constraint app_msg_size_c {
    en_app -> msg.size() > 0;
  }

  constraint kmac_app_c {
    if (en_app) {
      // application interface outputs 384-bit digest (48 bytes)
      output_len == kmac_pkg::AppDigestW / 8;

      // KMAC_APP will never use XOF mode
      xof_en == 0;
    }
  }

  constraint hash_mode_c {
    if (en_app) {
      if (app_mode == AppKeymgr) {
        kmac_en == 1;
      } else {
        kmac_en == 0;
      }
    } else {
      if (kmac_en) {
        hash_mode == sha3_pkg::CShake;
      } else {
        hash_mode != sha3_pkg::CShake;
      }
    }
  }

  virtual task pre_start();
    en_sideload_c.constraint_mode(0);
    super.pre_start();
  endtask

endclass
