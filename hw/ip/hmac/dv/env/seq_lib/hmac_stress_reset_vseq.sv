// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates random resets but when HMAC is doing some operations and mostly
// with long messages.
class hmac_stress_reset_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_stress_reset_vseq)

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : hmac_stress_reset_vseq


function hmac_stress_reset_vseq::new(string name="");
  super.new(name);
endfunction : new


task hmac_stress_reset_vseq::body();
  for (int i = 1; i <= num_trans; i++) begin
    run_seq_with_rand_reset_vseq(create_seq_by_name("hmac_long_msg_vseq"), 1, 100);
  end
endtask : body
