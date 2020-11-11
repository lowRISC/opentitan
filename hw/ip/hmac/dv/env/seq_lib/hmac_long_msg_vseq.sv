// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates a mix of short and long msgs
// Long msg has a larger size than HMAC input FIFO

class hmac_long_msg_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_long_msg_vseq)
  `uvm_object_new

  constraint msg_c {
    msg.size() dist {
        0             :/ 1,
        [1   :64]     :/ 1, // 64 bytes is the FIFO depth
        [65  :999]    :/ 1,
        [1000:3000]   :/ 6, // 1KB - 2KB according to SW immediate usage
        [3001:10_000] :/ 1  // temp set to 10KB as max length, spec max size is 2^64 bits
    };
  }

endclass : hmac_long_msg_vseq
