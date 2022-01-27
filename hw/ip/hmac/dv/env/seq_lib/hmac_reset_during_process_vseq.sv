// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates a mix of short and long msgs,
// and it injects reset during hmac process to try to interrupt hmac_core's `StPushToMsgFifo` FSM
// state.
// This sequence is not included in stress_all_with_rand_reset sequence, because stress_all
// sequence might disable the reset in current sequence.

class hmac_reset_during_process_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_reset_during_process_vseq)
  `uvm_object_new

  constraint msg_c {
    msg.size() dist {
        [65  :999]    :/ 1,
        [1000:3000]   :/ 8, // 1KB - 2KB according to SW immediate usage
        [3001:10_000] :/ 1  // temp set to 10KB as max length, spec max size is 2^64 bits
    };
  }

  function void pre_randomize();
    this.reset_during_hmac_process_c.constraint_mode(0);
  endfunction

endclass : hmac_reset_during_process_vseq
