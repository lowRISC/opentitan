// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// datapath_stress sequence will generate all message with size 1 and hmac_en
// thus will have 2 hashes (one for key, one for msg) with the shortest message required

class hmac_datapath_stress_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_datapath_stress_vseq)
  `uvm_object_new

  rand int nb_blk_msg;

  constraint nb_blk_msg_c {
    nb_blk_msg dist {
      0       :/1,
      [1:156] :/1
    };
  }

  constraint msg_c {
    solve digest_size before msg;
    if (digest_size == SHA2_256) {
      msg.size() == 1 + nb_blk_msg * HMAC_BLK_SIZE_SHA2_256;
    } else {
      msg.size() == 1 + nb_blk_msg * HMAC_BLK_SIZE_SHA2_384_512;
    }
  }

  constraint hmac_en_c {
    hmac_en == 1;
  }

  constraint sha_en_c {
    sha_en == 1;
  }

endclass : hmac_datapath_stress_vseq
