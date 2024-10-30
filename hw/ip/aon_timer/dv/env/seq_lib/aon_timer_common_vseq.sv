// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_common_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_common_vseq)

  extern constraint num_trans_c;

  extern function new (string name="");
  extern virtual task body();

endclass

constraint aon_timer_common_vseq::num_trans_c {
    num_trans inside {[1:2]};
}

function aon_timer_common_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask : body
