// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence is mainly used to run the CSR tests, there is no need to run multiple transactions
// in this sequence. Hence, the constraint is set to run only one transaction.
class ac_range_check_common_vseq extends ac_range_check_base_vseq;
  `uvm_object_utils(ac_range_check_common_vseq)

  // Constraints
  extern constraint num_trans_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task pre_start();
  extern task body();
endclass : ac_range_check_common_vseq


constraint ac_range_check_common_vseq::num_trans_c {
  num_trans == 1;
}

function ac_range_check_common_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_common_vseq::pre_start();
  do_ac_range_check_init = 1'b0;
  super.pre_start();
endtask : pre_start

task ac_range_check_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask : body
