// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates a mix of short and long msgs.
// During the transaction, this sequence randomly trigger wipe_secret and use scb to check if
// digest value has been updated.

class hmac_wipe_secret_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_wipe_secret_vseq)
  `uvm_object_new

  constraint msg_c {
    msg.size() dist {
        0             :/ 1,
        [1   :64]     :/ 1, // 64 bytes is the FIFO depth
        [65  :999]    :/ 1,
        [1000:3000]   :/ 7 // 1KB - 2KB according to SW immediate usage
    };
  }

  function void pre_randomize();
    this.wipe_secret_c.constraint_mode(0);
  endfunction

endclass : hmac_wipe_secret_vseq
