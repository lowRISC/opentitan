// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence tests error cases in HMAC and makes sure the core is not locked

class hmac_error_vseq extends hmac_long_msg_vseq;
  `uvm_object_utils(hmac_error_vseq)

  // Standard SV/UVM methods
  extern function new(string name="");
  extern function void pre_randomize();
  extern task pre_body();
endclass : hmac_error_vseq


function hmac_error_vseq::new(string name="");
  super.new(name);
endfunction : new

function void hmac_error_vseq::pre_randomize();
  this.legal_seq_c.constraint_mode(0);
endfunction : pre_randomize

task hmac_error_vseq::pre_body();
  // No need to trigger Save and Restore for this test
  cfg.save_and_restore_pct = 0;
  super.pre_body();
endtask : pre_body
