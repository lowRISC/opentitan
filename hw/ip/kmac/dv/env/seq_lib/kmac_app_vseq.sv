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
    msg.size() > 0;
  }

  constraint kmac_app_c {
    if (en_app) {
      // application interface outputs 256-bit digest (32 bytes)
      output_len == 32;

      // LC_CTRL uses 128-bit strength, KeyMgr and OTP_CTRL use 256-bit strength
      if (app_mode == AppLc) {
        strength == sha3_pkg::L128;
      } else {
        strength == sha3_pkg::L256;
      }

      // KMAC_APP will never use XOF mode
      xof_en == 0;
    }
  }

  constraint hash_mode_c {
    if (en_app) {
      hash_mode == sha3_pkg::CShake;
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

endclass
