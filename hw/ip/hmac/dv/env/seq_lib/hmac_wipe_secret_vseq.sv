// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates a mix of short and long msgs.
// During the transaction, this sequence randomly triggers wipe_secret and uses scb to check if
// digest value has been updated.
class hmac_wipe_secret_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_wipe_secret_vseq)

  // Constraints
  extern constraint msg_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern function void pre_randomize();
  extern task pre_body();
endclass : hmac_wipe_secret_vseq


constraint hmac_wipe_secret_vseq::msg_c {
  msg.size() dist {
    0             :/ 1,
    [1   :128]    :/ 1, // 128 bytes is the FIFO depth
    [119 :999]    :/ 1,
    [1000:3000]   :/ 7 // 1KB - 2KB according to SW immediate usage
  };
}

function hmac_wipe_secret_vseq::new(string name="");
  super.new(name);
endfunction : new

function void hmac_wipe_secret_vseq::pre_randomize();
  this.wipe_secret_c.constraint_mode(0);
endfunction : pre_randomize

task hmac_wipe_secret_vseq::pre_body();
  // No need to trigger Save and Restore for this test
  cfg.save_and_restore_pct = 0;
  super.pre_body();
endtask : pre_body
