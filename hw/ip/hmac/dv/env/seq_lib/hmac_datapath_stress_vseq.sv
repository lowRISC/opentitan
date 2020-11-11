// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// datapath_stress sequence will generate all message with size 1 and hmac_en
// thus will have 2 hashes (one for key, one for msg) with the shortest message required
// TODO: potentially use DV to check throughput here

class hmac_datapath_stress_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_datapath_stress_vseq)
  `uvm_object_new

  rand int msg_size_base;

  constraint msg_size_base_c {
    msg_size_base dist {
        0       :/1,
        [1:156] :/1
    };
  }

  constraint msg_c {
    msg.size() == 1 + msg_size_base * HMAC_HASH_SIZE;
  }

  constraint hmac_en_c {
    hmac_en == 1;
  }

  constraint sha_en_c {
    sha_en == 1;
  }

endclass : hmac_datapath_stress_vseq
